from flask import Flask, Response, stream_with_context
from flask_cors import CORS
import json
import time

app = Flask(__name__)
CORS(app)  # Apply CORS to all routes

def generate_tweet_stream():
    with open("tweets.json", "r") as file:
        for line in file:
            tweet = json.loads(line)
            yield f"data: {json.dumps(tweet)}\n\n"
            time.sleep(1)

@app.route("/stream_tweets", methods=["GET"])
def stream_tweets():
    headers = {
        "Content-Type": "text/event-stream",
        "Cache-Control": "no-cache",
        "Connection": "keep-alive",
    }
    return Response(stream_with_context(generate_tweet_stream()), headers=headers)

if __name__ == "__main__":
    app.run(host="127.0.0.1", port=3000, debug=True)
