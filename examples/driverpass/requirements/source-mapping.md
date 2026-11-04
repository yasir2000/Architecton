# Source-to-policy interpretation record

This example derives its scope from the supplied **CS 255 Business Requirements Document Template** and **CS 255 System Design Document Template** (DriverPass). These sources describe scheduling appointments, tracking available times and using Instructor/AppointmentSlot entities in UML, along with a payment/confirmation workflow.

**Directly represented by the example:** appointment availability and scheduling as a business domain; a distinct instructor and slot; the need to track changes and retain system logs.

**Additional analyst assumptions, not literal requirements from those documents:** an off-duty instructor must not accept slots; a single instructor cannot hold a duplicate slot ID; failed assignment must leave the roster unchanged. These are sensible but **added** constraints that require stakeholder validation before treating them as authoritative requirements. The normalized policy in `policy.json` defines their exact behavior.

**Deliberately excluded:** package purchase/payment validation, login/2FA, admin privileges, customer identity, actual time interval overlap, enterprise-wide resource conflicts, online/offline behavior, critical alerts and DMV notifications. These are present in the broader supplied case study but not implemented in this tiny formal slice.
