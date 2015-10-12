
def load_mem_file(filename, pack_bytes = 4):
	"""
	Load a mem file and return it as list. Pack pack_bytes into one word.
	The list contains integers packed from pack_bytes bytes. One byte is what
	the file stores in one string, where strings are separated by spaces and 
	newlines.
	"""
	import re

	rv = []
	f = open(filename, 'r')
	for full_line in f:
		# filter out comments
		r = re.match(r"(.*?)(//|#)(.*)", full_line)
		if r:
			line = r.group(1)
		else:
			line = full_line

		if line == '':
			continue

		pack_i = pack_bytes-1
		num = 0
		for w in re.finditer(r"([0-9a-fA-FxX]{2})+", line):
			if not ('x' in w.group(0) or 'X' in w.group(0)):
				num = (int(w.group(0), 16) << (pack_i*8)) + num

			if pack_i == 0:
				rv.append(num)
				pack_i = pack_bytes-1
				num = 0
			else:
				pack_i = pack_i-1

		if pack_i != pack_bytes-1:
			rv.append(num)

	return rv

def write_mem_file(filename, contents, dist_bytes = 4, byte_size = 8):
	"""
	Write a mem file named filename with the contents from contents.
	contents is a list of integers. Every member of contents is distributed to
	dist_bytes space separated strings of byte_size bit-length.
	"""
	max_words_per_line = 8
	words_per_line = 0

	f = open(filename, 'w')
	for w in contents:
		for i in reversed(range(dist_bytes)):
			by = (w >> (i*byte_size)) & (2**byte_size-1)
			# print "byte %i : %x" % (i, by)
			form = "%%0%ix " % int(byte_size/4)
			f.write(form % by)

			words_per_line = words_per_line + 1
			if words_per_line >= max_words_per_line:
				f.write("\n");
				words_per_line = 0

	f.close()
