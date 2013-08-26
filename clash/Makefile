
check: .PHONY
	$(IDRIS) --build clash.ipkg

recheck: clean check

install:
	$(IDRIS) --install clash.ipkg

clean: .PHONY
	$(IDRIS) --clean clash.ipkg

.PHONY:
