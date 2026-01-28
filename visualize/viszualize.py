import time
from influxdb_client import InfluxDBClient, Point
from influxdb_client.client.write_api import SYNCHRONOUS
import math


# Signal Tower Credentials
token = "my-super-secret-auth-token"
org = "math_lab"
bucket = "singmaster_data"
url = "http://localhost:8086"

client = InfluxDBClient(url=url, token=token, org=org)
write_api = client.write_api(write_options=SYNCHRONOUS)

def broadcast_pascal(rows):
    print(f"📡 Starting broadcast of {rows} signal layers...")
    for n in range(rows):
        val = 1
        for k in range(n + 1):
            # We treat the number value as the 'Signal Strength'
            # Use the log of the value so the "Big Computer" doesn't choke on huge numbers
            point = Point("pascal_signal") \
                .tag("row", str(n)) \
                .field("value", float(math.log10(val)) if val > 0 else 0.0)
            
            write_api.write(bucket=bucket, org=org, record=point)
            
            # Standard Pascal math for next coefficient
            val = val * (n - k) // (k + 1)
        print(f"✅ Layer {n} transmitted.")

if __name__ == "__main__":
    broadcast_pascal(50) # Bump this up to 500 or more!
    print("🎯 All signals pushed to the Lighthouse!")