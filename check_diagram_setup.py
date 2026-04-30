#!/usr/bin/env python3
"""Check whether pyncd diagram rendering prerequisites are running.

This helper validates:
- pyncd websocket server (default: localhost:8765)
- tsncd frontend dev server (default: localhost:5173)

It then prints concise next steps based on what is currently available.
"""

from __future__ import annotations

import argparse
import asyncio
import socket
from pathlib import Path

import websockets
from websockets.exceptions import WebSocketException


def is_port_open(host: str, port: int, timeout: float) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.settimeout(timeout)
        return sock.connect_ex((host, port)) == 0


async def is_websocket_open(host: str, port: int, timeout: float) -> bool:
    uri = f"ws://{host}:{port}"
    try:
        async with websockets.connect(uri, open_timeout=timeout):
            return True
    except (OSError, TimeoutError, ConnectionError, WebSocketException):
        return False


def find_tsncd_dir(repo_root: Path) -> Path | None:
    sibling = repo_root.parent / "tsncd"
    if sibling.exists() and sibling.is_dir():
        return sibling
    return None


def print_status_line(name: str, running: bool, host: str, port: int) -> None:
    state = "OK" if running else "MISSING"
    print(f"[{state}] {name}: {host}:{port}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Check local diagram rendering setup for pyncd")
    parser.add_argument("--ws-host", default="127.0.0.1", help="Websocket server host")
    parser.add_argument("--ws-port", type=int, default=8765, help="Websocket server port")
    parser.add_argument("--frontend-host", default="127.0.0.1", help="Frontend dev server host")
    parser.add_argument("--frontend-port", type=int, default=3000, help="Frontend dev server port")
    parser.add_argument("--timeout", type=float, default=0.4, help="Socket connect timeout in seconds")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent
    tsncd_dir = find_tsncd_dir(repo_root)

    ws_running = asyncio.run(is_websocket_open(args.ws_host, args.ws_port, args.timeout))
    frontend_running = is_port_open(args.frontend_host, args.frontend_port, args.timeout)

    print("Diagram setup status")
    print("--------------------")
    print_status_line("pyncd websocket server", ws_running, args.ws_host, args.ws_port)
    print_status_line("tsncd frontend", frontend_running, args.frontend_host, args.frontend_port)
    print()

    if ws_running and frontend_running:
        print("Everything looks ready.")
        print("Next:")
        print("1. Keep both servers running.")
        print("2. In pyncd, run: uv run minimum_working_example.py")
        print("3. Choose a command (for example, Transformer) to send data.")
        print("4. Refresh the tsncd page if needed.")
        return 0

    print("Next steps")
    print("----------")

    if not ws_running:
        print("Start websocket server from pyncd:")
        print("  uv run run_server.py")
        print()

    if not frontend_running:
        if tsncd_dir is not None:
            print("Start tsncd frontend:")
            print(f"  cd {tsncd_dir}")
            print("  npm install")
            print("  npm run dev")
            print()
        else:
            print("Start tsncd frontend (if not cloned yet):")
            print("  cd ..")
            print("  git clone https://github.com/mit-zardini-lab/tsncd")
            print("  cd tsncd")
            print("  npm install")
            print("  npm run dev")
            print()

    print("After both are running, open the frontend URL and run:")
    print("  uv run minimum_working_example.py")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
