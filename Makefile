COQPROJECT := _CoqProject
COQMF      := Makefile.coq
COQCONF    := $(COQMF).conf

.PHONY: all build clean distclean no-admit coqchk check

$(COQMF): $(COQPROJECT)
	@echo "[coq_makefile] generating $(COQMF)"
	@coq_makefile -f $(COQPROJECT) -o $(COQMF)

build: $(COQMF)
	@$(MAKE) -f $(COQMF) -j

clean:
	-@test -f $(COQMF) && $(MAKE) -f $(COQMF) clean 2>/dev/null || true
	-@rm -f $(COQMF) $(COQCONF)

distclean: clean
	-@rm -f coq/*.vo coq/*.vos coq/*.vok coq/*.glob coq/*.aux coq/.*.aux coq/*.d
	-@rm -f coq/.coqdeps.d
	-@rm -rf coq/.coq-native

no-admit:
	@! grep -R --line-number --fixed-strings "Admitted." coq || \
	  (echo "Found Admitted. above; please finish or remove." && exit 1)

coqchk: build
	@coqchk -Q coq Kube Kube.Model Kube.Scheduler Kube.Properties

check: build no-admit coqchk
all: check