import sys
import time

cnt = 0
while True :
    sys.stdout.write('\r%d' % cnt)
    sys.stdout.flush() 
    cnt = cnt + 1
    time.sleep(0.1)
    
