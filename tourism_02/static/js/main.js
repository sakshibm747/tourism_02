document.addEventListener('DOMContentLoaded', () => {
    // Basic Carousel Implementation
    const track = document.querySelector('.carousel-track');
    const prevBtn = document.querySelector('.prev-btn');
    const nextBtn = document.querySelector('.next-btn');

    if (track && prevBtn && nextBtn) {
        prevBtn.addEventListener('click', () => {
            track.scrollBy({ left: -300, behavior: 'smooth' });
        });

        nextBtn.addEventListener('click', () => {
            track.scrollBy({ left: 300, behavior: 'smooth' });
        });
    }

    // Default dates for the search form
    const departureInput = document.querySelector('input[name="departure"]');
    const returnInput = document.querySelector('input[name="return"]');

    if (departureInput && returnInput) {
        const today = new Date();
        const tomorrow = new Date(today);
        tomorrow.setDate(tomorrow.getDate() + 1);

        departureInput.valueAsDate = today;
        returnInput.valueAsDate = tomorrow;
    }

    // Dynamic Package Loading
    const packagesContainer = document.getElementById('dynamic-packages-container');
    if (packagesContainer) {
        fetch('/api/packages')
            .then(response => {
                if (!response.ok) throw new Error('Failed to load packages');
                return response.json();
            })
            .then(data => {
                packagesContainer.innerHTML = ''; // clear loading state

                // data is an object of packages, we convert it to an array
                const packages = Object.values(data);

                packages.forEach(pkg => {
                    // Create card element
                    const card = document.createElement('div');
                    card.className = 'deal-card';
                    // The core fix: assigning window.location href to the package id route correctly
                    card.onclick = () => window.location.href = `/package/${pkg.id}`;

                    card.innerHTML = `
                        <img src="${pkg.image}" 
                             alt="${pkg.title}" 
                             loading="lazy" 
                             decoding="async" 
                             onerror="this.onerror=null; this.src='https://images.unsplash.com/photo-1518182170546-0766de6b6aad?auto=format&fit=crop&w=500&q=80';">
                        <div class="deal-info">
                            <span class="deal-tag">${pkg.tag}</span>
                            <h3>${pkg.title}</h3>
                            <p>${pkg.duration}</p>
                            ${pkg.last_booked_label ? `<div class="social-proof-pill"><i class="fas fa-fire"></i> ${pkg.last_booked_label}</div>` : ''}
                            ${pkg.carbon_score ? `<div class="carbon-pill ${pkg.carbon_score.badge}"><i class="fas fa-leaf"></i> ${pkg.carbon_score.score}/100 • ${pkg.carbon_score.level}</div>` : ''}
                            <div class="deal-price">
                                <span class="old-price">₹${pkg.old_price.toLocaleString()}</span>
                                <span class="new-price">₹${pkg.price.toLocaleString()} <span class="discount">${pkg.discount}</span></span>
                            </div>
                        </div>
                    `;
                    packagesContainer.appendChild(card);
                });
            })
            .catch(error => {
                console.error("Error loading packages:", error);
                packagesContainer.innerHTML = `<div style="padding: 20px; color: red;">Failed to load travel packages. Please try again later.</div>`;
            });
    }

    // Agency in-app booking alerts (polling-based near real-time updates)
    const bellBtn = document.getElementById('agency-notification-bell');
    const dropdown = document.getElementById('agency-notification-dropdown');
    const countBadge = document.getElementById('agency-notification-count');
    const list = document.getElementById('agency-notification-list');
    const markAllBtn = document.getElementById('agency-mark-all-read');

    if (bellBtn && dropdown && countBadge && list) {
        const pollMs = parseInt(bellBtn.dataset.pollMs || '12000', 10);

        const escapeHtml = (value) => {
            return String(value || '')
                .replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&#39;');
        };

        const setUnreadCount = (count) => {
            if (count > 0) {
                countBadge.style.display = 'inline-flex';
                countBadge.textContent = count > 99 ? '99+' : String(count);
            } else {
                countBadge.style.display = 'none';
                countBadge.textContent = '0';
            }
        };

        const renderNotifications = (items) => {
            if (!Array.isArray(items) || items.length === 0) {
                list.innerHTML = '<div class="notification-empty">No alerts yet.</div>';
                return;
            }

            list.innerHTML = items.map((item) => {
                const unreadClass = item.is_read ? '' : 'unread';
                return `
                    <div class="notification-item ${unreadClass}" data-id="${escapeHtml(item.id)}">
                        <div class="notification-title">${escapeHtml(item.title || 'New Notification')}</div>
                        <div class="notification-message">${escapeHtml(item.message || '')}</div>
                        <div class="notification-time">${escapeHtml(item.created_at || '')}</div>
                    </div>
                `;
            }).join('');
        };

        const fetchNotifications = () => {
            fetch('/agency/notifications')
                .then((res) => {
                    if (!res.ok) throw new Error('Failed to fetch notifications');
                    return res.json();
                })
                .then((data) => {
                    setUnreadCount(data.unread_count || 0);
                    renderNotifications(data.notifications || []);
                })
                .catch((err) => {
                    console.error('Notification fetch error:', err);
                });
        };

        const markRead = (notificationId) => {
            const payload = notificationId ? { notification_id: notificationId } : {};
            return fetch('/agency/notifications/read', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify(payload)
            })
                .then((res) => {
                    if (!res.ok) throw new Error('Failed to mark notification read');
                    return res.json();
                })
                .then((data) => {
                    setUnreadCount(data.unread_count || 0);
                    fetchNotifications();
                })
                .catch((err) => {
                    console.error('Notification read error:', err);
                });
        };

        bellBtn.addEventListener('click', (event) => {
            event.stopPropagation();
            dropdown.style.display = dropdown.style.display === 'none' ? 'block' : 'none';
            if (dropdown.style.display === 'block') {
                fetchNotifications();
            }
        });

        document.addEventListener('click', (event) => {
            if (!dropdown.contains(event.target) && event.target !== bellBtn && !bellBtn.contains(event.target)) {
                dropdown.style.display = 'none';
            }
        });

        list.addEventListener('click', (event) => {
            const item = event.target.closest('.notification-item');
            if (!item) return;
            const notificationId = item.dataset.id;
            if (notificationId) {
                markRead(notificationId);
            }
        });

        if (markAllBtn) {
            markAllBtn.addEventListener('click', () => {
                markRead('');
            });
        }

        fetchNotifications();
        window.setInterval(fetchNotifications, Math.max(5000, pollMs));
    }
});
