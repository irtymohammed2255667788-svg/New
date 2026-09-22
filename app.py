"""Compatibility entry point for deployments that still run app.py."""

import runpy


if __name__ == "__main__":
    # bot.py keeps its async startup under its own __main__ guard.
    # Execute it as the main module so app.py behaves exactly like bot.py.
    runpy.run_module("bot", run_name="__main__")
