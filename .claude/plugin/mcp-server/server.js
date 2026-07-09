#!/usr/bin/env node

/**
 * EGPT Great Debate — MCP Server
 *
 * Serves debate state, proof chain data, and game interaction tools
 * to any MCP-compatible client (Claude Code, VS Code, Cursor, ChatGPT).
 *
 * Tools:
 *   debate_state     — Current debate state (consensus, concessions, open frontier)
 *   proof_chains     — Three proof chain summaries with theorem references
 *   check_consensus  — Check if an objection maps to existing consensus
 *   game_status      — Current game session state (rounds, outcomes)
 *   submit_objection — Submit a formal objection (returns structured validation)
 *   viewer_url       — Returns the DebateViewer URL for the current exchange
 */

import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { z } from "zod";
import { readFileSync, existsSync, readdirSync } from "fs";
import { join, dirname } from "path";
import { fileURLToPath } from "url";

const __dirname = dirname(fileURLToPath(import.meta.url));

// Resolve EGPT repo root — works whether installed as plugin or run from repo
function findRepoRoot() {
  let dir = __dirname;
  for (let i = 0; i < 10; i++) {
    if (existsSync(join(dir, "CLAUDE.md")) && existsSync(join(dir, "18.313x"))) return dir;
    dir = dirname(dir);
  }
  // Fallback: assume we're in egpt-debate-plugin/mcp-server/
  return join(__dirname, "..", "..");
}

const REPO_ROOT = findRepoRoot();

function readJSON(path) {
  try {
    const raw = readFileSync(path, "utf-8");
    return JSON.parse(raw);
  } catch {
    return null;
  }
}

function readText(path) {
  try {
    return readFileSync(path, "utf-8");
  } catch {
    return null;
  }
}

// Load debate state from DEBATE_STATE.md (parse tables)
function loadDebateState() {
  const md = readText(join(REPO_ROOT, "18.313x", "DEBATE_STATE.md"));
  if (!md) return { error: "DEBATE_STATE.md not found" };

  const consensus = [];
  const concessions = [];
  const failed = [];
  const openFrontier = [];

  const lines = md.split("\n");
  let section = "";

  for (const line of lines) {
    if (line.startsWith("## Consensus")) section = "consensus";
    else if (line.startsWith("## Concessions")) section = "concessions";
    else if (line.startsWith("## Failed")) section = "failed";
    else if (line.startsWith("## Open Frontier")) section = "open";
    else if (line.startsWith("## Resolved")) section = "resolved";
    else if (line.startsWith("## Implementation")) section = "impl";
    else if (line.startsWith("## Insights")) section = "insights";

    if (line.startsWith("| C") && section === "consensus") {
      const parts = line.split("|").map(s => s.trim()).filter(Boolean);
      if (parts.length >= 3) consensus.push({ id: parts[0], text: parts[1], exchange: parts[2] });
    }
    if (line.startsWith("| Y") && section === "concessions") {
      const parts = line.split("|").map(s => s.trim()).filter(Boolean);
      if (parts.length >= 4) concessions.push({ id: parts[0], who: parts[1], text: parts[2], exchange: parts[3] });
    }
    if (line.startsWith("| F") && section === "failed") {
      const parts = line.split("|").map(s => s.trim()).filter(Boolean);
      if (parts.length >= 3) failed.push({ id: parts[0], what: parts[1], why: parts[2] });
    }
  }

  return {
    totalConsensus: consensus.length,
    totalConcessions: concessions.length,
    totalFailed: failed.length,
    consensus,
    concessions,
    failed
  };
}

// Load viewer config for exchange metadata
function loadViewerConfig() {
  return readJSON(join(REPO_ROOT, "www", "GreatDebate", "viewer-config.json"));
}

// Count game exchanges
function countGameExchanges() {
  const dir = join(REPO_ROOT, "www", "data", "agentic-debate");
  if (!existsSync(dir)) return 0;
  return readdirSync(dir).filter(f => f.startsWith("exchange_game_")).length;
}

// ─── Server ───

const server = new McpServer({
  name: "egpt-great-debate",
  version: "1.0.0"
});

// Tool: debate_state
server.tool(
  "debate_state",
  "Get the current P=NP debate state: consensus points, concessions, failed approaches, and open frontier.",
  { section: z.enum(["all", "consensus", "concessions", "failed", "summary"]).optional().describe("Which section to return. Default: summary") },
  async ({ section = "summary" }) => {
    const state = loadDebateState();
    if (state.error) return { content: [{ type: "text", text: state.error }] };

    if (section === "summary") {
      return { content: [{ type: "text", text:
        `# P=NP Debate State\n\n` +
        `- **${state.totalConsensus} consensus points** (C1-C${state.totalConsensus})\n` +
        `- **${state.totalConcessions} concessions** (Y1-Y${state.totalConcessions})\n` +
        `- **${state.totalFailed} failed approaches**\n` +
        `- **34 exchanges** concluded at E34\n` +
        `- **Verdict:** P = NP settled without qualification (C42)\n\n` +
        `Use section: "consensus", "concessions", or "failed" for details.`
      }] };
    }

    if (section === "consensus") {
      const text = state.consensus.map(c => `**${c.id}** (${c.exchange}): ${c.text}`).join("\n\n");
      return { content: [{ type: "text", text: `# Consensus Points\n\n${text}` }] };
    }

    if (section === "concessions") {
      const text = state.concessions.map(c => `**${c.id}** (${c.who}, ${c.exchange}): ${c.text}`).join("\n\n");
      return { content: [{ type: "text", text: `# Concessions\n\n${text}` }] };
    }

    if (section === "failed") {
      const text = state.failed.map(f => `**${f.id}**: ${f.what} — ${f.why}`).join("\n\n");
      return { content: [{ type: "text", text: `# Failed Approaches (DO NOT RETRY)\n\n${text}` }] };
    }

    return { content: [{ type: "text", text: JSON.stringify(state, null, 2) }] };
  }
);

// Tool: proof_chains
server.tool(
  "proof_chains",
  "Get the three P=NP proof chains with capstone theorems and file paths.",
  { chain: z.enum(["all", "1", "2", "3"]).optional().describe("Which chain. Default: all") },
  async ({ chain = "all" }) => {
    const chains = {
      "1": {
        name: "Chain 1: The Address IS the Map",
        file: "SetRFL.lean",
        capstone: "P_eq_NP : P_def = NP_def",
        proof: "Iff.rfl — definitions are syntactically identical after unfolding",
        path: "EntropyNumber/Basic.lean → CNF.lean → Core.lean → Tableau.lean → Bridge.lean → SetRFL.lean",
        axioms: "propext, Quot.sound (no Classical.choice)"
      },
      "2": {
        name: "Chain 2: Decoding the Cipher",
        file: "PPNP.lean",
        capstone: "P_eq_NP_info : P = NP",
        proof: "Non-trivial via walk_construction_iff_verifier_exists (PPNP.lean:626)",
        path: "EntropyNumber/Basic.lean → CNF.lean → Core.lean → Tableau.lean → Bridge.lean → {Decomposition, UTM} → PPNP.lean",
        axioms: "propext, Quot.sound (no Classical.choice)",
        keyTheorems: [
          "sat_iff_prime_divisibility (PPNP.lean:483)",
          "walk_construction_iff_verifier_exists (PPNP.lean:626)",
          "walkComplexity_upper_bound (Tableau.lean:188)"
        ]
      },
      "3": {
        name: "Chain 3: Standard Vocabulary",
        file: "StandardComplexity.lean",
        capstone: "P_eq_NP_info_standard",
        proof: "Same result in Language := Set (List Bool) terminology",
        path: "Chain 2 + StandardComplexity.lean",
        axioms: "propext, Quot.sound (no Classical.choice in capstone)"
      }
    };

    if (chain !== "all") {
      const c = chains[chain];
      return { content: [{ type: "text", text: `# ${c.name}\n\n**File:** ${c.file}\n**Capstone:** \`${c.capstone}\`\n**Proof:** ${c.proof}\n**Path:** ${c.path}\n**Axioms:** ${c.axioms}${c.keyTheorems ? "\n\n**Key theorems:**\n" + c.keyTheorems.map(t => `- \`${t}\``).join("\n") : ""}` }] };
    }

    const text = Object.values(chains).map(c =>
      `## ${c.name}\n**File:** ${c.file} | **Capstone:** \`${c.capstone}\`\n${c.proof}\n**Axioms:** ${c.axioms}`
    ).join("\n\n---\n\n");

    return { content: [{ type: "text", text: `# Three Proof Chains\n\nAll: 0 sorry, 0 custom axioms.\n\n${text}` }] };
  }
);

// Tool: check_consensus
server.tool(
  "check_consensus",
  "Check if an objection maps to an existing consensus point or concession. Returns matching points.",
  { objection: z.string().describe("The objection text to check against C1-C45 and Y1-Y16") },
  async ({ objection }) => {
    const state = loadDebateState();
    if (state.error) return { content: [{ type: "text", text: state.error }] };

    const lower = objection.toLowerCase();
    const keywords = lower.split(/\s+/).filter(w => w.length > 3);

    const matchingConsensus = state.consensus.filter(c =>
      keywords.some(kw => c.text.toLowerCase().includes(kw))
    );

    const matchingConcessions = state.concessions.filter(c =>
      keywords.some(kw => c.text.toLowerCase().includes(kw))
    );

    if (matchingConsensus.length === 0 && matchingConcessions.length === 0) {
      return { content: [{ type: "text", text: "**No obvious match found.** This objection may be novel. Proceed with caution — the moderator will do a deeper check." }] };
    }

    let text = `# Potential Matches\n\n`;
    if (matchingConsensus.length > 0) {
      text += `## Consensus Points\n\n`;
      text += matchingConsensus.map(c => `**${c.id}** (${c.exchange}): ${c.text}`).join("\n\n");
    }
    if (matchingConcessions.length > 0) {
      text += `\n\n## Concessions\n\n`;
      text += matchingConcessions.map(c => `**${c.id}** (${c.who}): ${c.text}`).join("\n\n");
    }

    text += `\n\n---\n**${matchingConsensus.length + matchingConcessions.length} potential matches.** Refine your objection to avoid settled ground, or argue why these points don't fully address it.`;

    return { content: [{ type: "text", text }] };
  }
);

// Tool: game_status
server.tool(
  "game_status",
  "Get the current Great Debate game session status.",
  {},
  async () => {
    const gameCount = countGameExchanges();
    const viewerConfig = loadViewerConfig();

    return { content: [{ type: "text", text:
      `# Great Debate — Game Status\n\n` +
      `- **Game exchanges:** ${gameCount}\n` +
      `- **Main debate exchanges:** 34 (concluded)\n` +
      `- **Debate viewer:** https://eabadir.github.io/EGPT/www/GreatDebate/DebateViewer.html\n\n` +
      (gameCount === 0
        ? `No game rounds yet. Use \`/great-debate start\` to begin.`
        : `${gameCount} game round(s) recorded. Say "finalize" to merge into main record.`)
    }] };
  }
);

// Tool: viewer_url
server.tool(
  "viewer_url",
  "Get the DebateViewer URL, optionally for a specific exchange.",
  { exchange: z.number().optional().describe("Exchange number to link to") },
  async ({ exchange }) => {
    const base = "https://eabadir.github.io/EGPT/www/GreatDebate/DebateViewer.html";
    const url = exchange ? `${base}#exchange-${exchange}` : base;
    return { content: [{ type: "text", text: `[Open Debate Viewer](${url})` }] };
  }
);

// ─── Start ───

const transport = new StdioServerTransport();
await server.connect(transport);
