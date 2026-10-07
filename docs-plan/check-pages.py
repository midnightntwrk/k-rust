#!/usr/bin/env python3
"""Check that the curriculum ledger and the Vocs page graph stay aligned."""

from __future__ import annotations

import re
import sys
import tomllib
from collections import Counter
from html import unescape
from posixpath import dirname, join, normpath
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs-plan" / "tour.toml"
PAGES = ROOT / "docs-site" / "src" / "pages"
VOCS_CONFIG = ROOT / "docs-site" / "vocs.config.ts"
FACADE = ROOT / "crates" / "krs" / "src" / "lib.rs"
BUILTIN_FACADE = ROOT / "crates" / "krs" / "src" / "builtin.rs"
CLI_MAIN = ROOT / "crates" / "krs-cli" / "src" / "main.rs"


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
                    f"pages {previous.relative_to(ROOT)} and "
                    f"{page.relative_to(ROOT)} both define route {route}"
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


def main() -> None:
    with LEDGER.open("rb") as source:
        ledger = tomllib.load(source)

    chapters = ledger.get("chapter", [])
    syntheses = ledger.get("synthesis", [])
    lessons = ledger.get("lesson", [])
    concepts = ledger.get("concept", [])
    pages_by_route = documentation_pages()
    chapter_by_id = {chapter["id"]: chapter for chapter in chapters}
    concepts_by_chapter: dict[str, list[str]] = {
        chapter["id"]: [] for chapter in chapters
    }
    for concept in concepts:
        concepts_by_chapter.setdefault(concept["chapter"], []).append(concept["id"])
    declared_routes = (
        ["/"]
        + [chapter["route"] for chapter in chapters]
        + [synthesis["route"] for synthesis in syntheses]
        + [lesson["route"] for lesson in lessons]
    )
    duplicate_declared_routes = sorted(
        route for route, count in Counter(declared_routes).items() if count > 1
    )
    if duplicate_declared_routes:
        fail(f"duplicate routes in curriculum ledger: {duplicate_declared_routes}")
    known_routes = set(declared_routes)

    for chapter in chapters:
        chapter_id = chapter["id"]
        route = chapter["route"]
        page = page_for_route(route)
        if not page.is_file():
            fail(f"chapter {chapter_id!r} is missing page {page.relative_to(ROOT)}")
        source = page.read_text(encoding="utf-8")
        marker = re.search(r"\{/\*\s*tour-concepts:\s*([^*]*)\*/\}", source)
        declared = marker.group(1).split() if marker else []
        expected = concepts_by_chapter[chapter_id]
        if declared != expected:
            fail(
                f"chapter {chapter_id!r} concept marker differs from ledger: "
                f"expected {expected}, got {declared}"
            )

    for concept in concepts:
        chapter_id = concept["chapter"]
        if chapter_id not in chapter_by_id:
            fail(f"concept {concept['id']!r} has no canonical chapter route")

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
        if synthesis["status"] == "published":
            for concept_id in required:
                concept = next(
                    (item for item in concepts if item["id"] == concept_id), None
                )
                if concept is None:
                    fail(f"published synthesis requires unknown concept {concept_id!r}")
                destination = chapter_by_id[concept["chapter"]]["route"]
                if not page_for_route(destination).is_file():
                    fail(
                        f"published synthesis requirement {concept_id!r} "
                        f"has no page at {destination}"
                    )

    for lesson in lessons:
        lesson_page = page_for_route(lesson["route"])
        if not lesson_page.is_file():
            fail(f"lesson {lesson['id']!r} is missing page for {lesson['route']}")
        if "<BrowserLesson" not in lesson_page.read_text(encoding="utf-8"):
            fail(f"lesson {lesson['id']!r} page does not render <BrowserLesson />")

    config = VOCS_CONFIG.read_text(encoding="utf-8")
    sidebar_routes = re.findall(r"\blink:\s*['\"](/[^'\"]*)['\"]", config)
    duplicates = sorted(
        route for route, count in Counter(sidebar_routes).items() if count > 1
    )
    if duplicates:
        fail(f"duplicate primary-sidebar routes: {duplicates}")
    unknown_sidebar_routes = sorted(set(sidebar_routes) - known_routes)
    if unknown_sidebar_routes:
        fail(f"primary sidebar contains unknown routes: {unknown_sidebar_routes}")

    expected_chapter_routes = [
        chapter["route"] for chapter in sorted(chapters, key=lambda item: item["order"])
    ]
    actual_chapter_routes = [
        route for route in sidebar_routes if route in set(expected_chapter_routes)
    ]
    if actual_chapter_routes != expected_chapter_routes:
        fail(
            "primary sidebar does not contain chapter routes in ledger order: "
            f"expected {expected_chapter_routes}, got {actual_chapter_routes}"
        )

    for route, status in synthesis_routes.items():
        if status == "deferred" and route in sidebar_routes:
            fail(f"deferred synthesis route must stay out of primary sidebar: {route}")
        if status == "published" and route not in sidebar_routes:
            fail(f"published synthesis route is absent from primary sidebar: {route}")
        if status == "published" and sidebar_routes.index(route) <= max(
            sidebar_routes.index(chapter_route)
            for chapter_route in expected_chapter_routes
        ):
            fail(
                "published synthesis must follow every dependency-ordered chapter "
                f"in the primary sidebar: {route}"
            )

    for lesson in lessons:
        route = lesson["route"]
        if lesson["status"] == "deferred" and route in sidebar_routes:
            fail(f"deferred lesson route must stay out of primary sidebar: {route}")
        if lesson["status"] == "published" and route not in sidebar_routes:
            fail(f"published lesson route is absent from primary sidebar: {route}")

    actual_routes = set(pages_by_route)
    missing_routes = sorted(known_routes - actual_routes)
    if missing_routes:
        fail(f"curriculum routes have no page: {missing_routes}")
    undeclared_routes = sorted(actual_routes - known_routes)
    if undeclared_routes:
        fail(f"pages absent from the curriculum ledger: {undeclared_routes}")

    anchors_by_route = {
        route: anchors_for_page(page.read_text(encoding="utf-8"), route)
        for route, page in pages_by_route.items()
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
            if target_route not in known_routes:
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
    review = ledger.get("surface_review", {})
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
    if metadata_keys != ["k-namespace", "root", "syntax-root"]:
        fail("surface_review.metadata_keys must acknowledge the current facet shape")
    missing_metadata = [key for key in metadata_keys if f"`{key}`" not in composition]
    if missing_metadata:
        fail(f"composition page omits definition metadata keys: {missing_metadata}")

    print(
        f"tour pages passed: {len(chapters)} chapters, "
        f"{len(syntheses)} syntheses, {len(lessons)} lessons, {len(pages_by_route)} pages, "
        f"{len(sidebar_routes)} primary routes, {checked_links} internal links, "
        f"{checked_fragments} anchor links"
    )


if __name__ == "__main__":
    main()
