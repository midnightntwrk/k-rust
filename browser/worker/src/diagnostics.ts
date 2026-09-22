// Conversion of policy, expander, rustc, and collector output to Diagnostic.

import type { ExpandDiagnosticJson, LookupResponse, PolicyDiagnosticJson } from "./modules.ts";
import type { Diagnostic, MappingClass } from "./protocol.ts";
import type { RustcDiagnostic, RustcSpan } from "./rustc.ts";

export function fromPolicy(entry: PolicyDiagnosticJson): Diagnostic {
  return {
    origin: "policy",
    code: entry.code,
    severity: "error",
    message: entry.message,
    class: entry.class,
    authored: entry.authored ? { file: entry.file, start: entry.authored[0], end: entry.authored[1] } : null,
    generated: null,
  };
}

export function fromExpander(entry: ExpandDiagnosticJson): Diagnostic {
  return {
    // "protocol" diagnostics are request-shape errors inside the expander module.
    origin: entry.origin === "policy" ? "policy" : "expander",
    code: entry.code,
    severity: "error",
    message: entry.message,
    class: entry.class,
    authored: entry.authored ? { file: entry.file, start: entry.authored[0], end: entry.authored[1] } : null,
    generated: null,
    ...(entry.notes.length > 0 ? { rendered: [entry.message, ...entry.notes.map((note) => `note: ${note}`)].join("\n") } : {}),
  };
}

function severity(level: string): Diagnostic["severity"] {
  if (level === "warning") return "warning";
  if (level === "note" || level === "failure-note") return "note";
  if (level === "help") return "help";
  return "error";
}

export function primarySpan(diagnostic: RustcDiagnostic): RustcSpan | null {
  return diagnostic.spans.find((span) => span.is_primary) ?? diagnostic.spans[0] ?? null;
}

/**
 * The generated ranges to look up: the primary span of every diagnostic whose
 * primary span lies in the expanded file. Returns one entry per diagnostic
 * (null when the diagnostic has no span in that file).
 */
export function lookupRanges(diagnostics: RustcDiagnostic[], generatedFile: string): Array<[number, number] | null> {
  return diagnostics.map((diagnostic) => {
    const span = primarySpan(diagnostic);
    return span && span.file_name === generatedFile ? [span.byte_start, span.byte_end] : null;
  });
}

/**
 * rustc diagnostics in generated coordinates plus IR-10 lookup results for
 * their primary spans -> Diagnostic. The generated range is always retained;
 * only exact-authored and invocation-level mappings carry an authored range.
 */
export function fromRustc(
  diagnostics: RustcDiagnostic[],
  generatedFile: string,
  displayFile: string,
  mappings: LookupResponse["mappings"] | null,
): Diagnostic[] {
  const ranges = lookupRanges(diagnostics, generatedFile);
  let next = 0;
  return diagnostics.map((diagnostic, index) => {
    const span = primarySpan(diagnostic);
    let mappingClass: MappingClass = "unmappable";
    let authored: Diagnostic["authored"] = null;
    if (ranges[index]) {
      const mapping = mappings?.[next++];
      if (mapping) {
        mappingClass = mapping.class;
        if (mapping.authored && (mapping.class === "exact-authored" || mapping.class === "invocation-level")) {
          authored = { file: displayFile, start: mapping.authored[0], end: mapping.authored[1] };
        }
      }
    }
    return {
      origin: "rustc",
      code: diagnostic.code?.code ?? null,
      severity: severity(diagnostic.level),
      message: diagnostic.message,
      class: mappingClass,
      authored,
      generated: span ? { file: span.file_name, start: span.byte_start, end: span.byte_end } : null,
      ...(diagnostic.rendered ? { rendered: diagnostic.rendered } : {}),
    };
  });
}

/** The collector's `KRS collector failed: …` stderr (IR-18 refines this into CollectionError fields). */
export function fromCollector(stderr: string, trap: string | null): Diagnostic[] {
  const lines = stderr.split("\n").filter((line) => line.trim() !== "");
  const messages = lines.length > 0 ? lines : trap ? [trap] : [];
  return messages.map((message) => ({
    origin: "collector",
    code: null,
    severity: "error",
    message: message.replace(/^KRS collector failed: /, ""),
    class: "unmappable",
    authored: null,
    generated: null,
    rendered: message,
  }));
}
