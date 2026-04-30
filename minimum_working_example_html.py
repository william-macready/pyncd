import argparse
import asyncio
from datetime import datetime
from pathlib import Path
from typing import Callable
import html

import data_structure.Category as cat
import data_transfer.json as dtj
import display.node_category as dnc
import minimum_working_example as mwe
import websocket_transfer.websockets_transfer as wst
from websockets.exceptions import WebSocketException


DiagramFactory = Callable[[], cat.BroadcastedCategory]


def _render_html_document(
    title: str,
    ascii_diagram: str,
    json_payload: str,
    generated_at: str,
) -> str:
    safe_title = html.escape(title)
    safe_ascii = html.escape(ascii_diagram)
    safe_json = html.escape(json_payload)
    return f"""<!doctype html>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\" />
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />
  <title>{safe_title}</title>
  <style>
    :root {{
      --bg: #f7f5ee;
      --panel: #fffdf6;
      --ink: #1b1f23;
      --muted: #5f6b7a;
      --line: #c9c3b5;
      --accent: #2364aa;
    }}

    * {{ box-sizing: border-box; }}

    body {{
      margin: 0;
      font-family: "Iowan Old Style", "Palatino Linotype", Palatino, serif;
      color: var(--ink);
      background:
        radial-gradient(circle at 15% 0%, #fdf6df 0%, rgba(253, 246, 223, 0) 35%),
        radial-gradient(circle at 100% 80%, #e3f0ff 0%, rgba(227, 240, 255, 0) 30%),
        var(--bg);
      min-height: 100vh;
      padding: 28px 20px;
    }}

    .wrap {{
      max-width: 980px;
      margin: 0 auto;
      display: grid;
      gap: 14px;
    }}

    .card {{
      border: 1px solid var(--line);
      background: var(--panel);
      border-radius: 12px;
      box-shadow: 0 10px 24px rgba(0, 0, 0, 0.06);
      overflow: hidden;
    }}

    .header {{
      padding: 14px 18px;
      border-bottom: 1px solid var(--line);
      display: flex;
      justify-content: space-between;
      gap: 12px;
      align-items: baseline;
      flex-wrap: wrap;
    }}

    .title {{
      margin: 0;
      font-size: clamp(1.2rem, 2vw, 1.5rem);
      line-height: 1.2;
      letter-spacing: 0.01em;
    }}

    .meta {{
      color: var(--muted);
      font-family: "Menlo", "Consolas", "Liberation Mono", monospace;
      font-size: 0.82rem;
    }}

    .panel {{
      padding: 16px 18px;
    }}

    .section-title {{
      margin: 0 0 8px;
      font-size: 0.95rem;
      color: var(--accent);
      letter-spacing: 0.04em;
      text-transform: uppercase;
      font-family: "Helvetica Neue", "Arial", sans-serif;
      font-weight: 700;
    }}

    pre {{
      margin: 0;
      white-space: pre;
      overflow-x: auto;
      padding: 12px;
      border-radius: 8px;
      border: 1px solid var(--line);
      background: #faf8f0;
      font-size: 0.86rem;
      line-height: 1.33;
      font-family: "Menlo", "Consolas", "Liberation Mono", monospace;
    }}

    .footnote {{
      margin: 0;
      color: var(--muted);
      font-size: 0.9rem;
      line-height: 1.4;
      font-family: "Helvetica Neue", "Arial", sans-serif;
    }}
  </style>
</head>
<body>
  <main class=\"wrap\">
    <section class=\"card\">
      <header class=\"header\">
        <h1 class=\"title\">{safe_title}</h1>
        <span class=\"meta\">Generated: {html.escape(generated_at)}</span>
      </header>
      <div class=\"panel\">
        <h2 class=\"section-title\">Diagram (Text Form)</h2>
        <pre>{safe_ascii}</pre>
      </div>
      <div class=\"panel\">
        <h2 class=\"section-title\">JSON Payload</h2>
        <pre>{safe_json}</pre>
      </div>
      <div class=\"panel\">
        <p class=\"footnote\">This HTML file is a standalone export from pyncd. For full graphical rendering, run the tsncd frontend and send this same term to the websocket server.</p>
      </div>
    </section>
  </main>
</body>
</html>
"""


def export_term_to_html(name: str, term: cat.BroadcastedCategory, output_dir: Path) -> Path:
    output_dir.mkdir(parents=True, exist_ok=True)
    ascii_diagram = dnc.display_category(term).render()
    json_payload = dtj.TermJSONConverter.export_to_json(term, indent=2)
    generated_at = datetime.now().isoformat(timespec="seconds")
    html_content = _render_html_document(name, ascii_diagram, json_payload, generated_at)

    output_file = output_dir / (name.lower().replace(" ", "_") + ".html")
    output_file.write_text(html_content, encoding="utf-8")
    return output_file


def diagram_factories() -> list[tuple[str, DiagramFactory]]:
    return [
      ("Convolution Matrix", mwe.convolution_matrix),
      ("Convolution Full", mwe.convolution_full),
      ("Attention Core", mwe.attention_core),
      ("Attention Layer", mwe.attention_layer),
      ("FFN Layer", mwe.ffn_layer),
      ("Transformer", mwe.transformer),
    ]


def print_options(items: list[tuple[str, DiagramFactory]]) -> None:
    print("Available diagrams:")
    for i, (name, _) in enumerate(items):
        print(f"({i}) {name}")
    print("(a) Export all")
    print("(q) Quit")


async def maybe_send_to_websocket(term: cat.BroadcastedCategory, should_send: bool) -> None:
    if not should_send:
        return
    try:
        await wst.send_term(term)
        print("Sent term to websocket server.")
    except (OSError, ConnectionError, TimeoutError, WebSocketException) as exc:
        print(f"Could not send term to websocket server: {exc}")


async def interactive_export(output_dir: Path, send_ws: bool) -> None:
    items = diagram_factories()
    while True:
        print_options(items)
        choice = input("Select a diagram: ").strip().lower()
        if choice == "q":
            return
        if choice == "a":
            for name, factory in items:
                term = factory()
                target = export_term_to_html(name, term, output_dir)
                print(f"Exported {name} -> {target}")
                await maybe_send_to_websocket(term, send_ws)
            continue

        try:
            idx = int(choice)
            name, factory = items[idx]
        except (ValueError, IndexError):
            print("Invalid choice. Enter a number, 'a', or 'q'.")
            continue

        term = factory()
        target = export_term_to_html(name, term, output_dir)
        print(f"Exported {name} -> {target}")
        await maybe_send_to_websocket(term, send_ws)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export pyncd minimum working example diagrams to standalone HTML files"
    )
    parser.add_argument(
        "--output-dir",
        default="outputs/html",
        help="Directory where exported HTML files are written",
    )
    parser.add_argument(
        "--send-ws",
        action="store_true",
        help="Also send the selected term to the websocket server for tsncd rendering",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output_dir = Path(args.output_dir)
    asyncio.run(interactive_export(output_dir=output_dir, send_ws=args.send_ws))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
