VENV_PY := .venv/bin/python3
PYTHON ?= $(if $(wildcard $(VENV_PY)),$(VENV_PY),python3)
ELAN_LAKE := $(HOME)/.elan/bin/lake
LAKE ?= $(if $(wildcard $(ELAN_LAKE)),$(ELAN_LAKE),lake)
export PYTHONPATH := $(CURDIR)/python
CXXFLAGS ?= -O3
FLAGS := -std=c++17 -Wall -Wextra -Werror -Icpp/include
SOURCES := $(wildcard cpp/src/*.cpp)
HEADERS := $(wildcard cpp/include/qldpc/*.h cpp/include/qldpc/*.hpp cpp/src/*.hpp)

.PHONY: build proofs test verify benchmark-quick benchmark-full tail-latency figures export

build: build/libqldpc.so

build/libqldpc.so: $(SOURCES) $(HEADERS)
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

build/native-test: tests/native.cpp $(SOURCES) $(HEADERS)
	mkdir -p build
	$(CXX) $(CXXFLAGS) $(FLAGS) tests/native.cpp $(SOURCES) -o $@

test: build build/native-test
	./build/native-test
	$(PYTHON) -m unittest discover -s tests
	$(PYTHON) verification/verify_circuits.py
	$(PYTHON) verification/verify_distances.py

benchmark-quick: build
	$(PYTHON) benchmarks/run_external_benchmark.py --quick

benchmark-full: build
	$(PYTHON) benchmarks/run_external_benchmark.py --full --resume

tail-latency: build
	$(PYTHON) benchmarks/measure_tail_latency.py

figures: build
	$(PYTHON) benchmarks/render_plots.py --input benchmarks/results/waterfall_results.json --plots-dir docs/figures

verify: proofs test benchmark-quick
