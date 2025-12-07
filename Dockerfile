# Dockerfile for Sentinel Cloud Dashboard
FROM python:3.11-slim

# Install system dependencies
RUN apt-get update && apt-get install -y \
    verilator \
    make \
    git \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app

# Copy project files
COPY . .

# Install Python dependencies
RUN pip install --no-cache-dir \
    cocotb \
    streamlit \
    pandas \
    numpy \
    matplotlib \
    click \
    pydantic \
    pyyaml

# Expose Streamlit port
EXPOSE 8501

# Run dashboard
CMD ["streamlit", "run", "dashboard_v3.py", "--server.address=0.0.0.0", "--server.port=8501"]
