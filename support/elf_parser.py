#!/usr/bin/env python

class Elf_parser:
	"Extracts parts from ELF files"

	def __init__(self, filename):
		self.elf_file = filename

	def get_text(self):
		"Returns the text section of the ELF file as array"
		pass

	def get_data(self):
		"Returns the data section of the ELF file as array"
		pass

	def hex_dump_text(self):
		"Prints a hex dump of the text section"
		pass

	def hex_dump_data(self):
		"Prints a hex dump of the data section"
		pass
