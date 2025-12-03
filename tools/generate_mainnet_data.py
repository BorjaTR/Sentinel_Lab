import csv
import random
import time
from datetime import datetime, timedelta

def generate_solana_log(filename="data/solana_day_1.csv", num_tx=50000):
    print(f"🌊 Generating {num_tx} realistic 'Mainnet' transactions...")
    
    # 1. Create realistic "Wallet Addresses" (Strings)
    wallets = [f"SolAddress{i:04x}................" for i in range(1024)]
    
    # 2. Assign "Whale" status (Pareto Distribution)
    # The first 20 wallets do 80% of the volume
    whales = wallets[:20]
    minnows = wallets[20:]
    
    start_time = datetime.now() - timedelta(hours=24)
    
    with open(filename, 'w') as f:
        writer = csv.writer(f)
        writer.writerow(["timestamp", "signature", "sender", "receiver", "amount_usdc", "amount_compute"])
        
        current_time = start_time
        
        for i in range(num_tx):
            # Advance time (avg 50ms per tx on Solana)
            current_time += timedelta(milliseconds=random.randint(10, 100))
            ts_str = current_time.isoformat()
            
            sig = f"sig{random.getrandbits(64):016x}"
            
            # Pick Sender/Receiver based on Whale probability
            if random.random() < 0.8:
                sender = random.choice(whales)
            else:
                sender = random.choice(minnows)
                
            receiver = random.choice(wallets)
            while receiver == sender: receiver = random.choice(wallets)
            
            # Amount
            amt_usdc = random.randint(100, 100000)
            amt_compute = random.randint(10, 500)
            
            writer.writerow([ts_str, sig, sender, receiver, amt_usdc, amt_compute])
            
    print(f"✅ Data generated: {filename} ({num_tx} rows)")

if __name__ == "__main__":
    generate_solana_log()
