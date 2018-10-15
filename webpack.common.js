const webpack = require('webpack')
const path = require('path')

module.exports = {
  entry: './src/index.js',
  output: {
    path: path.join(__dirname, 'public'),
    filename: 'app.js'
  },
  module: {
    rules: [{
      test: /\.scss$/,
      use: [{
        loader: "style-loader" // creates style nodes from JS strings
      },
      {
        loader: "css-loader?modules&localIdentName=[name]__[local]___[hash:base64:5]" // translates CSS into CommonJS
      },
      {
        loader: "sass-loader" // compiles Sass to CSS
      }]
    }, {
      test: /\.js$/,
      use: { loader: 'babel-loader' }
    }]
  },
  plugins: []
}