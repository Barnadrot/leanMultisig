# Error: a range loop with start > end has no consistent trace (iteration count
# is end - start mod p), so it is rejected at VM execution.
def main():
    for i in range(5, 3):
        print(i)
    return
