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

/**
 * A KRS code spelling (`krs::<stage>::<name>`, each component lowercase words
 * joined by `-`), the shape every code in krs-diagnostic's registry has.
 */
const TAGGED_MESSAGE = /^\[(krs::[a-z][a-z0-9]*(?:-[a-z0-9]+)*::[a-z][a-z0-9]*(?:-[a-z0-9]+)*)\] /;

/**
 * Splits a rustc message spelled by krs-diagnostic's `tag_rustc_message`
 * (`[code] message`, how a KRS proc macro's `compile_error!` carries its code)
 * into its code and message, as `krs check` does. Any other message, bracketed
 * or not, returns null. The worker has no copy of the code registry, so it
 * accepts any well-formed KRS spelling where `krs check` also requires the code
 * to be registered.
 */
export function untagRustcMessage(message: string): { code: string; message: string } | null {
  const match = TAGGED_MESSAGE.exec(message);
  return match ? { code: match[1]!, message: message.slice(match[0].length) } : null;
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
 * rustc's rendered header `level: [code] message` -> `level[code]: message`,
 * the form rustc uses for its own codes and `krs check` for KRS codes.
 * Any other rendering is returned unchanged.
 */
function untagRendered(rendered: string, level: string, code: string): string {
  const header = `${level}: [${code}] `;
  return rendered.startsWith(header) ? `${level}[${code}]: ${rendered.slice(header.length)}` : rendered;
}

/**
 * rustc diagnostics in generated coordinates plus krs-expand lookup results for
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
    // A KRS proc macro's `compile_error!` carries its code in the message; rustc's own code wins.
    const tagged = diagnostic.code ? null : untagRustcMessage(diagnostic.message);
    return {
      origin: "rustc",
      code: diagnostic.code?.code ?? tagged?.code ?? null,
      severity: severity(diagnostic.level),
      message: tagged?.message ?? diagnostic.message,
      class: mappingClass,
      authored,
      generated: span ? { file: span.file_name, start: span.byte_start, end: span.byte_end } : null,
      ...(diagnostic.rendered ? { rendered: tagged ? untagRendered(diagnostic.rendered, diagnostic.level, tagged.code) : diagnostic.rendered } : {}),
    };
  });
}

/** The collector's `KRS collector failed: …` stderr. CollectionError's Display carries only the detail, so no code is available. */
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
