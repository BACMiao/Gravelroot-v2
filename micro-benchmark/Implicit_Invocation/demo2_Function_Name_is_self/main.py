# main.py

from base import Chain

def main():
    chain = Chain(initial_value="print('Hello World!')")
    chain.run(5)

if __name__ == "__main__":
    main()
