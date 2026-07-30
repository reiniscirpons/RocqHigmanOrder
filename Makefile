INDIR := ./theories
OUTDIR := ./html
SOURCES := $(wildcard $(INDIR)/*.v)
OUTPUTS := $(patsubst $(INDIR)/%.v,$(OUTDIR)/%.html,$(SOURCES))

.PHONY: all clean install html

all install: Makefile.coq
	$(MAKE) -f $< $@

clean: Makefile.coq
	$(MAKE) -f $< $@
	rm -rf $(OUTDIR)/

%.vo: Makefile.coq %.v
	$(MAKE) -f $< $@

Makefile.coq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@


%: Makefile.coq
	$(MAKE) -f $< $@

html: $(OUTPUTS)

$(OUTDIR)/%.html: $(INDIR)/%.v
	alectryon --frontend coq+rst --backend webpage $< -o $@
