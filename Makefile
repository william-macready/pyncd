PYTHON := uv run
TSNCD_DIR := ../tsncd

.PHONY: help diagram-check diagram-server diagram-example diagram-html diagram-html-ws diagram-run diagram-frontend

help:
	@echo "Available targets:"
	@echo "  make diagram-check    # Check websocket/frontend availability"
	@echo "  make diagram-server   # Start pyncd websocket server"
	@echo "  make diagram-example  # Start minimum working example CLI"
	@echo "  make diagram-html     # Export standalone HTML diagram files"
	@echo "  make diagram-html-ws  # Export HTML files and also send to websocket"
	@echo "  make diagram-run      # Check setup, then start minimum working example"
	@echo "  make diagram-frontend # Start tsncd frontend (if ../tsncd exists)"

diagram-check:
	@$(PYTHON) check_diagram_setup.py

diagram-server:
	@$(PYTHON) run_server.py

diagram-example:
	@$(PYTHON) minimum_working_example.py

diagram-html:
	@$(PYTHON) minimum_working_example_html.py

diagram-html-ws:
	@$(PYTHON) minimum_working_example_html.py --send-ws

diagram-run:
	@$(PYTHON) check_diagram_setup.py; \
	status=$$?; \
	if [ $$status -eq 0 ]; then \
		$(PYTHON) minimum_working_example.py; \
	else \
		echo "Setup not ready. Run 'make diagram-frontend' (and/or 'make diagram-server') first."; \
		exit $$status; \
	fi

diagram-frontend:
	@if [ -d "$(TSNCD_DIR)" ]; then \
		if lsof -tiTCP:3000 -sTCP:LISTEN >/dev/null; then \
			echo "tsncd frontend appears to already be running on port 3000."; \
			echo "Open http://localhost:3000 in your browser."; \
		else \
			cd "$(TSNCD_DIR)" && npm install && npm run dev; \
		fi; \
	else \
		echo "tsncd repo not found at $(TSNCD_DIR)."; \
		echo "Clone it with:"; \
		echo "  cd .. && git clone https://github.com/mit-zardini-lab/tsncd"; \
		exit 1; \
	fi
