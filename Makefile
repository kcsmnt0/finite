AGDA=agda
PYTHON=python3

SOURCES := src/**/*.agda

all: finite.agda-lib generate-everything.py $(SOURCES)
	rm -f src/Everything.agda
	$(PYTHON) generate-everything.py > src/Everything.agda
	$(AGDA) src/Everything.agda

clean:
	rm -f src/Everything.agda
