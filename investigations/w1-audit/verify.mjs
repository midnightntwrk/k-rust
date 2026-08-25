import { readFileSync } from "node:fs";

const matrix = JSON.parse(readFileSync(new URL("./capabilities.json", import.meta.url), "utf8"));
const required = [
  "id",
  "parent_capability_group",
  "description",
  "roadmap_track",
  "dependencies",
  "coupled_cluster_or_owner",
  "current_oracle_grade",
  "candidate_target_oracle_grade",
  "candidate_acceptance_command_or_missing_command_marker",
  "evidence_references",
  "status",
  "unknowns"
];
const expectedGroups = [
  "IN-01", "IN-02", "IN-03", "IN-04", "IN-05", "IN-06", "IN-07",
  "IP-01", "IP-02", "IP-03", "IP-04", "IP-05", "IP-06", "IP-07", "IP-08",
  "CF-01", "CF-02", "CF-03", "CF-04",
  "LO-01", "LO-02", "LO-03", "LO-04", "LO-05", "LO-06", "LO-07", "LO-08", "LO-09",
  "KO-01", "KO-02", "KO-03", "KO-04", "KO-05", "KO-06", "KO-07", "KO-08", "KO-09", "KO-10",
  "PR-01", "PR-02", "PR-03", "SP-01"
];
const errors = [];
const ids = new Set();
for (const row of matrix.candidate_leaves) {
  for (const key of required) if (!(key in row)) errors.push(`${row.id ?? "<no-id>"}: missing ${key}`);
  if (ids.has(row.id)) errors.push(`duplicate id ${row.id}`);
  ids.add(row.id);
  if (!["G1", "C1", "C2", "optional"].includes(row.roadmap_track)) errors.push(`${row.id}: invalid track`);
  if (!/^O[0-4]$/.test(row.current_oracle_grade)) errors.push(`${row.id}: invalid current grade`);
  if (!/^O[0-4]$/.test(row.candidate_target_oracle_grade)) errors.push(`${row.id}: invalid target grade`);
}
const represented = new Set(matrix.candidate_leaves.map(row => row.parent_capability_group));
const missingGroups = expectedGroups.filter(group => !represented.has(group));
if (missingGroups.length) errors.push(`missing census groups: ${missingGroups.join(", ")}`);
if (expectedGroups.length !== matrix.top_level_census_count) errors.push("declared census count mismatch");
const g1 = matrix.candidate_leaves.filter(row => row.roadmap_track === "G1");
const g1MissingCommands = g1.filter(row => row.candidate_acceptance_command_or_missing_command_marker.startsWith("missing-command"));
const summary = {
  verdict: errors.length ? "fail" : "pass",
  candidateRows: matrix.candidate_leaves.length,
  representedTopLevelGroups: expectedGroups.length - missingGroups.length,
  tracks: Object.fromEntries(["G1", "C1", "C2", "optional"].map(track => [track, matrix.candidate_leaves.filter(row => row.roadmap_track === track).length])),
  g1Rows: g1.length,
  g1MissingDeterministicAcceptanceCommands: g1MissingCommands.length,
  g1MissingCommandIds: g1MissingCommands.map(row => row.id),
  errors
};
console.log(JSON.stringify(summary, null, 2));
if (errors.length) process.exit(1);
