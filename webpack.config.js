const path = require("path");
const ReactRefreshWebpackPlugin = require('@pmmmwh/react-refresh-webpack-plugin');
const CopyPlugin = require('copy-webpack-plugin');

/** @type {(env: any) => import('webpack').Configuration} */
module.exports = env => {
  const environment = process.env.NODE_ENV
  const isDevelopment = environment === 'development'

  const babelOptions = {
      presets: ['@babel/preset-env', '@babel/preset-react', '@babel/preset-typescript'],
    plugins: [
      isDevelopment && require.resolve('react-refresh/babel'),
    ].filter(Boolean),
  };

  global.$RefreshReg$ = () => {};
  global.$RefreshSig$ = () => () => {};

  return {
    entry: ["./client/src/index.tsx"],
    mode: isDevelopment ? 'development' : 'production',
    module: {
      rules: [
        {
          test: /\.(js|jsx)$/,
          exclude: [/server/, /node_modules/],
          use: [{
            loader: require.resolve('babel-loader'),
            options: babelOptions,
          }]
        },
        {
          test: /\.tsx?$/,
          use: [{
            loader: 'ts-loader',
            options: { allowTsInNodeModules: true }
          }],
          exclude: /(node_modules\/(?!lean4))|(server\/)/, // Allow .ts imports from node_modules/lean4
        },
        {
          test: /\.css$/,
          use: ["style-loader", "css-loader"]
        },
        {
          test: /\.svg$/i,
          issuer: /\.[jt]sx?$/,
          use: [{
            loader: "@svgr/webpack",
            options: { dimensions: false }
          }],
        },
      ]
    },
    resolve: {
      extensions: ["*", ".js", ".jsx", ".tsx", ".ts"],
      fallback: {
        "http": require.resolve("stream-http") ,
         "path": require.resolve("path-browserify")
        },
    },
    output: {
      path: path.resolve(__dirname, "client/dist/"),
      filename: "bundle.js",
    },
    devServer: {
      proxy: {
        '/websocket': {
           target: 'ws://localhost:8080',
           ws: true
        },
      },
      static: path.join(__dirname, 'client/public/'),
      port: 3000,
      hot: true,
    },
    devtool: "source-map",
    plugins: [
      new CopyPlugin({
        patterns: [{
          context: path.resolve(__dirname, 'client', 'public'),
          from: 'index.html',
        }, {
          context: path.resolve(__dirname, 'client', 'public'),
          from: 'onigasm.wasm',
        }, {
          context: path.resolve(__dirname, 'client', 'public', 'examples'),
          from: '**/*',
          to: 'examples/',
        }, {
          context: path.resolve(path.dirname(require.resolve('@leanprover/infoview/package.json')), 'dist'),
          from: '*.production.min.js',
        }]
      }),
      isDevelopment && new ReactRefreshWebpackPlugin(),
    ].filter(Boolean)
  };
}
