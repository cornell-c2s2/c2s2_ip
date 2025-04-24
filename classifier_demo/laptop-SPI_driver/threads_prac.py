import threading
import time

# Create a shared Event object for stopping
stop_event = threading.Event()

def say_hello():
    while not stop_event.is_set():
        print("Hello World")
        time.sleep(1)

def say_johnny():
    while not stop_event.is_set():
        print("Here's Johnny!")
        time.sleep(1)

# Create threads
thread1 = threading.Thread(target=say_hello)
thread2 = threading.Thread(target=say_johnny)

# Start threads
thread1.start()
thread2.start()

try:
    while True:
        time.sleep(0.1)  # Let the main thread idle
except KeyboardInterrupt:
    print("\nStopping threads...")
    stop_event.set()  # Signal threads to stop

# Wait for threads to finish
thread1.join()
thread2.join()
print("All threads stopped.")
