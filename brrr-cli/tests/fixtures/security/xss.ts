// Test fixtures for XSS detection
// Contains various XSS vulnerability patterns

// VULNERABLE: Direct innerHTML assignment
function vulnerableInnerHtml(userInput: string): void {
    const div = document.getElementById('content');
    // VULNERABLE: User input to innerHTML
    div!.innerHTML = userInput;
}

// VULNERABLE: Template literal to innerHTML
function vulnerableTemplateInnerHtml(name: string): void {
    const container = document.querySelector('.container');
    // VULNERABLE: User input interpolated to innerHTML
    container!.innerHTML = `<div>Hello, ${name}!</div>`;
}

// VULNERABLE: document.write with user input
function vulnerableDocumentWrite(data: string): void {
    // VULNERABLE: document.write with user input
    document.write(data);
}

// VULNERABLE: eval with user input
function vulnerableEval(code: string): unknown {
    // VULNERABLE: eval with user controlled code
    return eval(code);
}

// VULNERABLE: outerHTML assignment
function vulnerableOuterHtml(userContent: string): void {
    const element = document.getElementById('target');
    // VULNERABLE: outerHTML with user input
    element!.outerHTML = userContent;
}

// SAFE: textContent assignment
function safeTextContent(userInput: string): void {
    const div = document.getElementById('content');
    // SAFE: textContent sanitizes input
    div!.textContent = userInput;
}

// SAFE: createElement and appendChild
function safeCreateElement(text: string): void {
    const div = document.createElement('div');
    div.textContent = text;
    document.body.appendChild(div);
}

// SAFE: setAttribute for safe attributes
function safeSetAttribute(value: string): void {
    const input = document.getElementById('myInput') as HTMLInputElement;
    // SAFE: Setting value attribute
    input.setAttribute('value', value);
}

// SAFE: Constants only
function safeConstantHtml(): void {
    const div = document.getElementById('content');
    // SAFE: No user input
    div!.innerHTML = '<p>Static content</p>';
}
