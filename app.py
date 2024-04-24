from flask import Flask, render_template, request
from interpreter import generate_html

app = Flask(__name__,static_url_path='/static')

@app.route('/', methods=['GET', 'POST'])
def index():
    if request.method == 'GET':
        # Serve HTML page for GET request
        return render_template('index.html')
    elif request.method == 'POST':
        # Call function to generate HTML for POST request with HTML content from textarea
        code_content = request.form['code_content']
        generate_html(code_content)
        return render_template("typethong-info.html")


if __name__ == '__main__':
    app.run(debug=True)
