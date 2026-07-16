.PHONY: audit-agent

audit-agent:
ifndef TARGET
	$(error usage: make audit-agent TARGET=codex-cli SRC=examples/codex-cli-fixture [MODE=extract|replay-committed])
endif
ifeq ($(MODE),replay-committed)
else
ifndef SRC
	$(error usage: make audit-agent TARGET=codex-cli SRC=examples/codex-cli-fixture [MODE=extract|replay-committed])
endif
endif
	cargo build --release --bin legitimacy-audit-agent
	target/release/legitimacy-audit-agent --target $(TARGET) $(if $(MODE),--mode $(MODE),) $(SRC) $(ARGS) || echo "audit-agent: non-zero exit is the expected outcome for a rejected harness"
