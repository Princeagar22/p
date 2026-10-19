FROM python:3.11-slim

# Prevent python from buffering stdout and stderr
ENV PYTHONUNBUFFERED=1

WORKDIR /app

# Install dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy bot files
COPY . .

# Run bot
CMD ["python", "-u", "main.py"]
