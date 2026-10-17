#!/usr/bin/env python3
"""Check that the curriculum ledger and the Vocs page graph stay aligned."""

from __future__ import annotations

import re
import sys
from collections import Counter
from html import unescape
from posixpath import dirname, join, normpath
from pathlib import Path
from urllib.parse import unquote, urlsplit


from ledger import KRS, PLAN, Ledger


SITE = PLAN.parent
PAGES = SITE / "src" / "pages"
VOCS_CONFIG = SITE / "vocs.config.ts"
FACADE = KRS / "crates" / "krs" / "src" / "lib.rs"
BUILTIN_FACADE = KRS / "crates" / "krs" / "src" / "builtin.rs"
CLI_MAIN = KRS / "crates" / "krs-cli" / "src" / "main.rs"


def fail(message: str) -> None:
    print(f"tour pages: {message}", file=sys.stderr)
    raise SystemExit(1)


def page_for_route(route: str) -> Path:
    if route == "/":
        stem = PAGES / "index"
        stems = (stem,)
    else:
        stem = PAGES / route.removeprefix("/")
        stems = (stem, stem / "index")
    for candidate_stem in stems:
        for suffix in (".mdx", ".md"):
            candidate = candidate_stem.with_suffix(suffix)
            if candidate.is_file():
                return candidate
    return stem.with_suffix(".mdx")


def route_for_page(page: Path) -> str:
    relative = page.relative_to(PAGES).with_suffix("")
    if relative.name == "index":
        parent = relative.parent.as_posix()
        if parent != ".":
            return f"/{parent}"
        return "/"
    return f"/{relative.as_posix()}"


def documentation_pages() -> dict[str, Path]:
    pages: dict[str, Path] = {}
    for suffix in ("*.md", "*.mdx"):
        for page in sorted(PAGES.rglob(suffix)):
            route = route_for_page(page)
            previous = pages.get(route)
            if previous is not None:
                fail(
                    f"pages {previous.relative_to(SITE)} and "
                    f"{page.relative_to(SITE)} both define route {route}"
                )
            pages[route] = page
    return pages


def mask_fenced_code(source: str) -> str:
    """Mask fenced code while preserving lines for diagnostics."""
    masked: list[str] = []
    fence: tuple[str, int] | None = None
    for line in source.splitlines(keepends=True):
        marker = re.match(r"^[ \t]{0,3}(`{3,}|~{3,})", line)
        if fence is not None:
            masked.append("\n" if line.endswith("\n") else "")
            if (
                marker
                and marker.group(1)[0] == fence[0]
                and len(marker.group(1)) >= fence[1]
            ):
                fence = None
            continue
        if marker:
            fence = (marker.group(1)[0], len(marker.group(1)))
            masked.append("\n" if line.endswith("\n") else "")
            continue
        masked.append(line)
    return "".join(masked)


def mask_code(source: str) -> str:
    source = mask_fenced_code(source)
    return re.sub(r"(`+)(?:(?!\1).)*?\1", "", source)


def heading_slug(heading: str) -> str:
    heading = re.sub(r"<[^>]+>", "", heading)
    heading = re.sub(r"!\[([^]]*)\]\([^)]*\)", r"\1", heading)
    heading = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", heading)
    heading = re.sub(r"[*_~`]", "", heading)
    heading = unescape(heading).strip().lower()
    heading = re.sub(r"[^\w -]", "", heading)
    return heading.replace(" ", "-")


def anchors_for_page(source: str, route: str) -> set[str]:
    masked = mask_code(source)
    heading_source = mask_fenced_code(source)
    anchors: set[str] = set()
    slug_occurrences: dict[str, int] = {}
    explicit_ids = re.findall(
        r"\bid\s*=\s*(?:[\"']([^\"']+)[\"']|\{\s*[\"']([^\"']+)[\"']\s*\})",
        masked,
    )
    for choices in explicit_ids:
        anchor = next(choice for choice in choices if choice)
        if anchor in anchors:
            fail(f"duplicate anchor on {route}: #{anchor}")
        anchors.add(anchor)

    for line in heading_source.splitlines():
        match = re.match(r"^ {0,3}#{1,6}[ \t]+(.+?)[ \t]*$", line)
        if match is None:
            continue
        heading = re.sub(r"[ \t]+#+[ \t]*$", "", match.group(1))
        base = heading_slug(heading)
        anchor = base
        while anchor in slug_occurrences:
            slug_occurrences[base] = slug_occurrences.get(base, 0) + 1
            anchor = f"{base}-{slug_occurrences[base]}"
        slug_occurrences[anchor] = 0
        if anchor in anchors:
            fail(f"duplicate anchor on {route}: #{anchor}")
        anchors.add(anchor)
    return anchors


def internal_links(source: str) -> list[tuple[str, int]]:
    masked = mask_code(source)
    patterns = (
        re.compile(
            r"\[[^]\n]*\]\(\s*(?:<([^>\n]+)>|([^\s)]+))"
            r"(?:\s+(?:\"[^\"]*\"|'[^']*'|\([^)]*\)))?\s*\)"
        ),
        re.compile(
            r"(?m)^ {0,3}\[[^]\n]+\]:\s*(?:<([^>\n]+)>|([^\s]+))"
        ),
        re.compile(
            r"\b(?:href|to)\s*=\s*(?:[\"']([^\"']+)[\"']|"
            r"\{\s*[\"']([^\"']+)[\"']\s*\})"
        ),
    )
    links: list[tuple[str, int]] = []
    for pattern in patterns:
        for match in pattern.finditer(masked):
            target = next(value for value in match.groups() if value is not None)
            links.append((unescape(target), masked.count("\n", 0, match.start()) + 1))
    return sorted(links, key=lambda item: item[1])


def resolve_internal_link(target: str, source_route: str) -> tuple[str, str] | None:
    parsed = urlsplit(target)
    if parsed.scheme or parsed.netloc or target.startswith("//"):
        return None
    path = unquote(parsed.path)
    if not path:
        route = source_route
    elif path.startswith("/"):
        route = normpath(path)
    else:
        route = normpath(join(dirname(source_route), path))
        if not route.startswith("/"):
            route = f"/{route}"
    if route.endswith((".md", ".mdx")):
        route = route.rsplit(".", 1)[0]
    route = route.rstrip("/") or "/"
    return route, unquote(parsed.fragment)


def concept_marker(page: Path) -> list[str]:
    marker = re.search(r"\{/\*\s*tour-concepts:\s*([^*]*)\*/\}", page.read_text(encoding="utf-8"))
    return marker.group(1).split() if marker else []


def main() -> None:
    ledger = Ledger.load()
    pages = [page for page in sorted(ledger.rows("page"), key=lambda row: row["order"]) if not page["retired"]]
    retired = [page for page in ledger.rows("page") if page["retired"]]
    lessons = sorted(ledger.rows("lesson"), key=lambda row: row["order"])
    written = [lesson for lesson in lessons if lesson["status"] != "planned"]
    syntheses = ledger.rows("synthesis")
    browser_lessons = ledger.rows("browser_lesson")
    topics = ledger.rows("topic")
    pages_by_route = documentation_pages()
    # The /k-rust section mirrors k-rust's documentation (docs-site/scripts/sync-k-rust.py) and is
    # no part of the tour curriculum; links into it are still checked.
    other_pages = {
        route: page for route, page in pages_by_route.items()
        if route == "/k-rust" or route.startswith("/k-rust/")
    }
    pages_by_route = {route: page for route, page in pages_by_route.items() if route not in other_pages}
    declared_routes = (
        ["/"]
        + [page["route"] for page in pages]
        + [lesson["route"] for lesson in written]
        + [synthesis["route"] for synthesis in syntheses]
        + [lesson["route"] for lesson in browser_lessons]
    )
    duplicate_declared_routes = sorted(
        route for route, count in Counter(declared_routes).items() if count > 1
    )
    if duplicate_declared_routes:
        fail(f"duplicate routes in curriculum ledger: {duplicate_declared_routes}")
    known_routes = set(declared_routes)

    for lesson in lessons:
        if lesson["status"] == "planned" and page_for_route(lesson["route"]).is_file():
            fail(f"planned lesson {lesson['id']!r} already has a page at {lesson['route']}")
    for page in retired:
        if page_for_route(page["route"]).is_file():
            fail(f"retired page {page['id']!r} still exists at {page['route']}")

    # Every page and written lesson declares exactly the topics whose destination it is.
    topics_by_destination: dict[str, list[str]] = {}
    for topic in topics:
        topics_by_destination.setdefault(ledger.destination(topic), []).append(topic["id"])
    hosts = [(f"page {page['id']!r}", page["route"]) for page in pages] + [
        (f"lesson {lesson['id']!r}", lesson["route"]) for lesson in written
    ]
    for label, route in hosts:
        page = page_for_route(route)
        if not page.is_file():
            fail(f"{label} is missing page {page.relative_to(SITE)}")
        expected = topics_by_destination.get(route, [])
        declared = concept_marker(page)
        if declared != expected:
            fail(f"{label} concept marker differs from ledger: expected {expected}, got {declared}")
    hosted = {route for _, route in hosts}
    homeless = sorted(set(topics_by_destination) - hosted)
    if homeless:
        fail(f"topic destinations that are no published page: {homeless}")

    synthesis_routes: dict[str, str] = {}
    for synthesis in syntheses:
        route = synthesis["route"]
        synthesis_routes[route] = synthesis["status"]
        synthesis_page = page_for_route(route)
        if not synthesis_page.is_file():
            fail(f"synthesis {synthesis['id']!r} is missing page for {route}")
        synthesis_source = synthesis_page.read_text(encoding="utf-8")
        marker = re.search(r"\{/\*\s*synthesis-concepts:\s*([^*]*)\*/\}", synthesis_source)
        declared = marker.group(1).split() if marker else []
        required = synthesis.get("requires", [])
        if declared != required:
            fail(
                f"synthesis {synthesis['id']!r} concept marker differs from ledger: "
                f"expected {required}, got {declared}"
            )
        annotated = re.findall(r'<ConceptGloss\s+concept="([^"]+)"', synthesis_source)
        if annotated != required:
            fail(
                f"synthesis {synthesis['id']!r} glosses differ from ledger: "
                f"expected {required}, got {annotated}"
            )

    for lesson in browser_lessons:
        lesson_page = page_for_route(lesson["route"])
        if not lesson_page.is_file():
            fail(f"browser lesson {lesson['id']!r} is missing page for {lesson['route']}")
        if "<BrowserLesson" not in lesson_page.read_text(encoding="utf-8"):
            fail(f"browser lesson {lesson['id']!r} page does not render <BrowserLesson />")

    config = VOCS_CONFIG.read_text(encoding="utf-8")
    sidebar_routes = [
        route for route in re.findall(r"\blink:\s*['\"](/[^'\"]*)['\"]", config)
        if route not in other_pages
    ]
    duplicates = sorted(
        route for route, count in Counter(sidebar_routes).items() if count > 1
    )
    if duplicates:
        fail(f"duplicate primary-sidebar routes: {duplicates}")
    unknown_sidebar_routes = sorted(set(sidebar_routes) - known_routes)
    if unknown_sidebar_routes:
        fail(f"primary sidebar contains unknown routes: {unknown_sidebar_routes}")

    for label, expected_routes in (
        ("pages", [page["route"] for page in pages]),
        ("lessons", [lesson["route"] for lesson in written]),
    ):
        actual = [route for route in sidebar_routes if route in set(expected_routes)]
        if actual != expected_routes:
            fail(
                f"primary sidebar does not contain the ledger's {label} in ledger order: "
                f"expected {expected_routes}, got {actual}"
            )

    for route, status in synthesis_routes.items():
        if status == "deferred" and route in sidebar_routes:
            fail(f"deferred synthesis route must stay out of primary sidebar: {route}")
        if status == "published" and route not in sidebar_routes:
            fail(f"published synthesis route is absent from primary sidebar: {route}")

    for lesson in browser_lessons:
        route = lesson["route"]
        if lesson["status"] == "deferred" and route in sidebar_routes:
            fail(f"deferred browser lesson route must stay out of primary sidebar: {route}")
        if lesson["status"] == "published" and route not in sidebar_routes:
            fail(f"published browser lesson route is absent from primary sidebar: {route}")

    actual_routes = set(pages_by_route)
    missing_routes = sorted(known_routes - actual_routes)
    if missing_routes:
        fail(f"curriculum routes have no page: {missing_routes}")
    undeclared_routes = sorted(actual_routes - known_routes)
    if undeclared_routes:
        fail(f"pages absent from the curriculum ledger: {undeclared_routes}")

    anchors_by_route = {
        route: anchors_for_page(page.read_text(encoding="utf-8"), route)
        for route, page in {**pages_by_route, **other_pages}.items()
    }
    linked_routes: set[str] = set(sidebar_routes)
    checked_links = 0
    checked_fragments = 0
    for source_route, page in sorted(pages_by_route.items()):
        source = page.read_text(encoding="utf-8")
        for target, line in internal_links(source):
            resolved = resolve_internal_link(target, source_route)
            if resolved is None:
                continue
            target_route, fragment = resolved
            checked_links += 1
            if target_route not in known_routes and target_route not in other_pages:
                fail(
                    f"dead internal link from {source_route}:{line}: {target} "
                    f"(resolved to {target_route})"
                )
            if target_route != source_route:
                linked_routes.add(target_route)
            if fragment:
                checked_fragments += 1
                if fragment not in anchors_by_route[target_route]:
                    fail(
                        f"dead anchor link from {source_route}:{line}: {target} "
                        f"(no #{fragment} on {target_route})"
                    )

    orphan_routes = sorted(actual_routes - linked_routes - {"/"})
    if orphan_routes:
        fail(
            "orphan pages are neither in primary navigation nor linked from a page: "
            f"{orphan_routes}"
        )

    facade = FACADE.read_text(encoding="utf-8")
    reference = page_for_route("/reference/language").read_text(encoding="utf-8")
    review = ledger.raw.get("surface_review", {})
    macro_exports_match = re.search(
        r"pub use krs_macros::\{(?P<exports>.*?)\};", facade, re.DOTALL
    )
    if macro_exports_match is None:
        fail("could not locate the public krs_macros facade exports")
    macro_exports = {
        item.strip()
        for item in macro_exports_match.group("exports").split(",")
        if item.strip()
    }
    if sorted(macro_exports) != review.get("macro_exports"):
        fail(
            "public macro exports changed without refreshing surface_review.macro_exports"
        )
    missing_macros = sorted(
        name for name in macro_exports if f"k::{name}" not in reference
    )
    if missing_macros:
        fail(f"language reference omits public macro exports: {missing_macros}")

    if "pub mod builtin;" not in facade:
        fail("could not locate the public builtin facade module")
    builtin_source = BUILTIN_FACADE.read_text(encoding="utf-8")
    builtin_aliases = set(
        re.findall(r"pub use (?:self::)?[A-Za-z_][A-Za-z0-9_]* as ([a-z][a-z0-9_]*);", builtin_source)
    )
    if sorted(builtin_aliases) != review.get("builtin_operations"):
        fail(
            "builtin operation aliases changed without refreshing "
            "surface_review.builtin_operations"
        )
    missing_builtins = sorted(
        name for name in builtin_aliases if f"`{name}`" not in reference
    )
    if missing_builtins:
        fail(f"language reference omits builtin operation aliases: {missing_builtins}")

    cli_source = CLI_MAIN.read_text(encoding="utf-8")
    cli_commands = ["fmt"] + re.findall(
        r'"(check|expand|emit-k|build|parse|run|search|prove)"\s*=>\s*CommandKind::', cli_source
    )
    if cli_commands != review.get("cli_commands"):
        fail("CLI commands changed without refreshing surface_review.cli_commands")
    workflow = page_for_route("/reference/workflow").read_text(encoding="utf-8")
    missing_commands = [command for command in cli_commands if f"`{command}`" not in workflow]
    if missing_commands:
        fail(f"workflow reference omits CLI commands: {missing_commands}")

    composition = page_for_route("/advanced/composition").read_text(encoding="utf-8")
    metadata_keys = review.get("metadata_keys")
    if metadata_keys != ["k-namespace", "int-literals", "allow-raw-k", "profile"]:
        fail("surface_review.metadata_keys must acknowledge the current facet shape")
    missing_metadata = [key for key in metadata_keys if f"`{key}`" not in composition]
    if missing_metadata:
        fail(f"composition page omits definition metadata keys: {missing_metadata}")

    print(
        f"tour pages passed: {len(pages)} earlier pages, {len(written)} written lessons, "
        f"{len(syntheses)} syntheses, {len(browser_lessons)} browser lessons, {len(pages_by_route)} pages, "
        f"{len(sidebar_routes)} primary routes, {checked_links} internal links, "
        f"{checked_fragments} anchor links"
    )


if __name__ == "__main__":
    main()
