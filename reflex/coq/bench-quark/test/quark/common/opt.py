import optparse

def parse_options(argv):
    global options
    parser = optparse.OptionParser()
    parser.add_option("-l", action="store_true", dest="use_length_encoding")
    parser.add_option("-m", action="store_true", dest="use_shm")
    parser.add_option("-k", action="store_true", dest="use_kcookies")
    (options, _) = parser.parse_args(argv)
