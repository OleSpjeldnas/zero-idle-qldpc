VENV_PY := .venv/bin/python3
PYTHON ?= $(if $(wildcard $(VENV_PY)),$(VENV_PY),python3)
ELAN_LAKE := $(HOME)/.elan/bin/lake
LAKE ?= $(if $(wildcard $(ELAN_LAKE)),$(ELAN_LAKE),lake)
export PYTHONPATH := $(CURDIR)/python
CXXFLAGS ?= -O3
FLAGS := -std=c++17 -Wall -Wextra -Werror -Iinclude
SOURCES := $(wildcard src/*.cpp)

.PHONY: build proofs test verify benchmark-quick benchmark-full plots export

build: build/libqldpc.so

build/libqldpc.so: $(SOURCES) $(wildcard include/qldpc/*.h include/qldpc/*.hpp src/*.hpp)
	mkdir -p build
	$(CXX) $(CXXFLAGS) $(FLAGS) -shared -fPIC $(SOURCES) -o $@

export: build
	$(PYTHON) -m zero_idle_qldpc.export

proofs:
	@if command -v $(LAKE) >/dev/null 2>&1; then \
		cd proofs && $(LAKE) build && $(LAKE) exe verify-proofs; \
	else \
		echo "Note: Lean 4 (lake) not found in PATH; skipping formal proof build."; \
	fi

build/native-test: tests/native.cpp $(SOURCES) $(wildcard include/qldpc/* src/*.hpp)
	mkdir -p build
	$(CXX) $(CXXFLAGS) $(FLAGS) tests/native.cpp $(SOURCES) -o $@

test: build build/native-test
	./build/native-test
	$(PYTHON) -m unittest discover -s tests
	$(PYTHON) verify_circuit_cert.py
	$(PYTHON) verify_distance_bounds.py

benchmark-quick: build
	$(PYTHON) benchmarks/run_external_benchmark.py --quick

benchmark-full: build
	$(PYTHON) benchmarks/run_external_benchmark.py --full --resume

plots:
	$(PYTHON) benchmarks/render_plots.py --input benchmarks/results/waterfall_results.json --plots-dir plots

verify: proofs test benchmark-quick
