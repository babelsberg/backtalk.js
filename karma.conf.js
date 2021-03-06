module.exports = function(config) {
    config.set({
        frameworks: ['browserify', 'mocha'],
        files: [
            'node_modules/babelify/node_modules/babel-core/browser-polyfill.js',
            "*.js"
        ],
        reporters: ['progress'],
        port: 9876,
        colors: true,
        // possible values: config.LOG_DISABLE || config.LOG_ERROR || config.LOG_WARN || config.LOG_INFO || config.LOG_DEBUG
        logLevel: config.LOG_INFO,
        autoWatch: true,
        browsers: ['PhantomJS'],
        singleRun: false,
        preprocessors: {
            "*.js": ["browserify"]
        },
        "browserify": {
            debug: true,
            transform: ['babelify']
        },
    });
};
