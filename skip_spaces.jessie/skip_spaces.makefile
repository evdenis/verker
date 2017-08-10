# this makefile was automatically generated; do not edit 

TIMEOUT ?= 10

WHYLIB ?= /home/work/.opam/4.04.2/lib/jessie

USERWHYTHREEOPT=

JESSIE3CONF ?= $(WHYLIB)/why3/why3.conf

why3ml: skip_spaces.mlw
	 why3 $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3ide: skip_spaces.mlw
	 why3 ide $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3replay: skip_spaces.mlw
	 why3 replay $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3autoreplay: skip_spaces.mlw
	 why3 replay -q -f --obsolete-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3typecheck: skip_spaces.mlw
	 why3 prove --type-only $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3prove: skip_spaces.mlw
	 why3 prove $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

why3sprove: skip_spaces.mlw
	 why3 sprove --clean --strategy default $(USERWHYTHREEOPT) --extra-config $(JESSIE3CONF) $<

