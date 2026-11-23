def get_tank(x):
    """Extract ascent fuel (a) and odd core (M) from x = 2^a * M - 1."""
    temp = x + 1
    a = 0
    while temp % 2 == 0:
        temp //= 2
        a += 1
    return a, temp

def analyze_number(start_n):
    """Print the full accelerated wave trajectory for any odd integer."""
    x = start_n
    print(f"=== Wave Map for {start_n} ===")
    wave = 0
    while x > 1:
        wave += 1
        a, M = get_tank(x)
        num = (3**a) * M - 1
        e = 1
        while num % 2 == 0:
            num //= 2
            e += 1
        a_next, _ = get_tank(num) if num > 1 else (0, 1)
        print(f"Wave {wave:2d} | {x:<6} (a={a}, M={M:<5}) -> break e={e} -> {num:<6} (a_next={a_next})")
        x = num

def find_records(limit=50000):
    """Search for record-holding integers requiring the most waves to drop below start_n."""
    print(f"\n=== Searching for Wave Records up to {limit} ===")
    max_waves = 0
    for start in range(3, limit, 2):
        x = start
        waves = 0
        while x >= start:
            waves += 1
            a, M = get_tank(x)
            num = (3**a) * M - 1
            while num % 2 == 0:
                num //= 2
            x = num
        if waves > max_waves:
            max_waves = waves
            print(f"New Record: {start:<6} required {max_waves:2d} waves to drop below start")

if __name__ == "__main__":
    # 1. Analyze trajectory of 27
    analyze_number(27)
    
    # 2. Search for wave records up to 50,000
    find_records(50000)
