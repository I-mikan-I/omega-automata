INPUTS := $(wildcard *.dot)
OUTPUTS := $(basename $(INPUTS))
OUTPUTS := $(addsuffix .svg,$(OUTPUTS) )

all: $(OUTPUTS)

%.svg: %.dot
	dot -Tsvg -x $< > $@

.PHONY: clean

clean:
	rm -rf $(addsuffix .svg,$(basename $(INPUTS)))