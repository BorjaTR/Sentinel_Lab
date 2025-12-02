class LedgerModel:
    def __init__(self, num_users=1024, initial_balance=1000):
        self.balances = {i: initial_balance for i in range(num_users)}

    def process_transaction(self, sender, receiver, amount):
        """
        Updates Python state and returns (success, new_sender_bal, new_receiver_bal)
        """
        # 1. Self-transfer check
        if sender == receiver:
            return True, self.balances[sender], self.balances[receiver]

        # 2. Solvency Check
        if self.balances[sender] < amount:
            return False, self.balances[sender], self.balances[receiver]

        # 3. Execute
        self.balances[sender] -= amount
        self.balances[receiver] += amount

        return True, self.balances[sender], self.balances[receiver]
