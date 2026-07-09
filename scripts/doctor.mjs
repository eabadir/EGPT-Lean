#!/usr/bin/env node
// Great Debate kit doctor — answers "am I correctly installed, and do my citations resolve?"
// Run from the kit root: node scripts/doctor.mjs
// Exit 0 = all checks pass; exit 1 = at least one FAIL (each FAIL prints its fix).
import { existsSync, readFileSync, readdirSync } from 'node:fs';
import { execSync } from 'node:child_process';
import { join } from 'node:path';

const root = process.cwd();
let failures = 0;
const pass = (msg) => console.log(`PASS  ${msg}`);
const fail = (msg, fix) => { failures++; console.log(`FAIL  ${msg}\n      fix: ${fix}`); };

// 1. Am I the project root?
const rootFiles = ['.mcp.json', 'CLAUDE.md', '.claude/skills/great-debate/SKILL.md', '.claude/agents'];
const missingRoot = rootFiles.filter((f) => !existsSync(join(root, f)));
if (missingRoot.length === 0) {
    pass('kit root: all kit files present at cwd');
} else {
    fail(`kit root: missing ${missingRoot.join(', ')} at ${root}`,
        'run the doctor from the kit root (the directory holding .mcp.json); in Claude Code, OPEN the kit directory as your project root or its .claude/ will not auto-load');
}

// 2. Is the local MCP wired and installed?
try {
    const mcp = JSON.parse(readFileSync(join(root, '.mcp.json'), 'utf8'));
    const servers = Object.keys(mcp.mcpServers || {});
    if (servers.length === 1 && servers[0] === 'egpt-great-debate') {
        pass('.mcp.json: exactly one server, egpt-great-debate (local stdio)');
    } else {
        fail(`.mcp.json: servers = [${servers.join(', ')}] — expected exactly [egpt-great-debate]`,
            'the kit must wire ONLY the local debate MCP; anything else breaks the participant-plane air-gap');
    }
} catch (e) {
    fail(`.mcp.json unreadable: ${e.message}`, 'restore .mcp.json from the kit');
}
if (existsSync(join(root, '.claude/plugin/mcp-server/node_modules'))) {
    pass('debate MCP: node_modules installed');
} else {
    fail('debate MCP: node_modules missing — the egpt-great-debate server cannot start',
        'cd .claude/plugin/mcp-server && npm install');
}

// 3. Do the record files the skills cite actually resolve? (kit overlays an EGPT working tree)
const RECORD_FILES = [
    '18.313x/DEBATE_STATE.md',
    'Lean/PROOF_CHAINS.md',
    'PeqNP_SKEPTICS_GUIDE.md',
];
const missingRecords = RECORD_FILES.filter((f) => !existsSync(join(root, f)));
if (missingRecords.length === 0) {
    pass('record files: all skill-cited debate records resolve from kit root');
} else {
    fail(`record files absent: ${missingRecords.join(', ')}`,
        'this kit OVERLAYS an EGPT working tree — copy the kit files onto an EGPT checkout (or seed a repo with both); the debate MCP and skills read these records relative to the project root');
}

// 4. Air-gap: no org-backend references in wiring/instruction surfaces (README excluded — it documents the ban)
try {
    execSync(
        `grep -rEn --exclude-dir=node_modules "\\bunk-[a-z]|descix chat|DESCIX_API_URL|beast_[a-z]|dev\\.descix\\.net|admin-login|mcpServers.*descix|\\.descix/sessions" .claude .mcp.json CLAUDE.md`,
        { cwd: root, stdio: 'pipe' }
    );
    fail('air-gap: org-backend references found in kit wiring/instruction files (grep matched)',
        're-run the grep without -c to see the lines; the kit must carry zero control-plane references');
} catch (e) {
    if (e.status === 1) pass('air-gap: zero org-backend references in .claude/, .mcp.json, CLAUDE.md');
    else fail(`air-gap grep errored: ${e.message}`, 'run the README isolation grep manually');
}

// 5. Evidence Contract vendored copy present and marker-framed
const ec = join(root, '.claude/EVIDENCE_CONTRACT.md');
if (existsSync(ec)) {
    const t = readFileSync(ec, 'utf8');
    if (t.includes('EVIDENCE-CONTRACT:BEGIN') && t.includes('EVIDENCE-CONTRACT:END')) {
        pass('Evidence Contract: vendored copy present with conformance markers (byte-parity vs the canonical module is checked in the org repo CI, scripts/verify-evidence-contract.mjs)');
    } else {
        fail('Evidence Contract: vendored copy lacks BEGIN/END conformance markers',
            're-vendor from the canonical module (descix-platform-api evidence-contract.js) via the org repo conformance script with --write');
    }
} else {
    fail('.claude/EVIDENCE_CONTRACT.md missing', 're-vendor from the canonical module');
}

// 6. Agent files: frontmatter name must match filename stem
const agentsDir = join(root, '.claude/agents');
if (existsSync(agentsDir)) {
    let mismatches = 0;
    for (const f of readdirSync(agentsDir).filter((f) => f.endsWith('.md'))) {
        const m = readFileSync(join(agentsDir, f), 'utf8').match(/^name:\s*(\S+)/m);
        const stem = f.replace(/\.agent\.md$|\.md$/, '');
        if (m && m[1] !== stem) {
            mismatches++;
            fail(`agent naming: ${f} declares name '${m[1]}' (filename says '${stem}')`,
                `rename the file to ${m[1]}.agent.md or fix the frontmatter — one identity per role`);
        }
    }
    if (mismatches === 0) pass('agent naming: every agent file matches its declared name');
}

console.log(failures === 0
    ? '\nDOCTOR: ALL CHECKS PASSED — say /facilitator to begin.'
    : `\nDOCTOR: ${failures} check(s) FAILED — fix the lines above before starting.`);
process.exit(failures === 0 ? 0 : 1);
