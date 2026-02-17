//! BindingRegistry: singleton registry for binding detectors.

use std::sync::OnceLock;

use crate::bindings::detector::BindingDetector;
use crate::bindings::detectors;

static BINDING_REGISTRY: OnceLock<BindingRegistry> = OnceLock::new();

/// Registry of all binding system detectors.
pub struct BindingRegistry {
    detectors: Vec<Box<dyn BindingDetector>>,
}

impl BindingRegistry {
    /// Get the global binding registry singleton.
    pub fn global() -> &'static Self {
        BINDING_REGISTRY.get_or_init(Self::new)
    }

    fn new() -> Self {
        let detectors: Vec<Box<dyn BindingDetector>> = vec![
            Box::new(detectors::rust_ffi::RustFfiDetector),
            Box::new(detectors::cgo::CGoDetector),
            Box::new(detectors::jni::JniDetector),
            Box::new(detectors::napi::NapiDetector),
            Box::new(detectors::ctypes::CtypesDetector),
            Box::new(detectors::pybind11::Pybind11Detector),
            Box::new(detectors::cuda::CudaDispatchDetector),
            Box::new(detectors::torch_library::TorchLibraryDetector),
        ];
        Self { detectors }
    }

    /// Get all detectors applicable to a given language.
    pub fn detectors_for_language(&self, language: &str) -> Vec<&dyn BindingDetector> {
        self.detectors
            .iter()
            .filter(|d| d.applicable_languages().contains(&language))
            .map(|d| d.as_ref())
            .collect()
    }
}
