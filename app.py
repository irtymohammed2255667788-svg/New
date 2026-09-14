"""Compatibility entry point for deployments that still run app.py."""

# bot.py contains the actual application and starts it at module load.
# Keeping this shim lets Railway deployments configured as `python app.py`
# run the same code as the repository's Procfile (`python bot.py`).
import bot  # noqa: F401
