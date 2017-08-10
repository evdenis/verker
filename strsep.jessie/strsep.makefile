# this makefile was automatically generated; do not edit 

TIMEOUT ?= 10

WHYLIB ?= /home/work/.opam/4.04.2/lib/jessie

USERWHYTHREEOPT=

JESSIE3CONF ?= $(WHYLIB)/why3/why3.conf

why3ml: strsep.mlw
	 why3 $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3ide: strsep.mlw
	 why3 ide $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3replay: strsep.mlw
	 why3 replay $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3autoreplay: strsep.mlw
	 why3 replay -q -f --obsolete-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3typecheck: strsep.mlw
	 why3 prove --type-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3prove: strsep.mlw
	 why3 prove $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3sprove: strsep.mlw
	 why3 sprove --clean --strategy default $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

