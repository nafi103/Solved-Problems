#pragma GCC optimize("Ofast")
#include <bits/stdc++.h>
using namespace std;
using ll = long long;
#define int long long
 void Solve()
{
    string a;
    cin >> a;
    ll n = a.size();
    set<ll> ind[26];
    for (int i = n - 1; i >= 0; i--)
        ind[a[i] - 'A'].insert(i);
    vector<array<int, 3>> icp;
    while (1) {
        if (ind['I' - 'A'].empty())
            break;
        ll i = *ind['I' - 'A'].begin();
        ind['I' - 'A'].erase(ind['I' - 'A'].begin());
         if (ind['C' - 'A'].empty())
            break;
        auto it = ind['C' - 'A'].upper_bound(i);
        if (it == ind['C' - 'A'].end())
            break;
        ll c1 = *it;
        ind['C' - 'A'].erase(it);
         it = ind['P' - 'A'].upper_bound(c1);
        if (it == ind['P' - 'A'].end())
            break;
        ll p = *it;
        ind['P' - 'A'].erase(it);
         // if (ind['C' - 'A'].empty() || *ind['C' - 'A'].rbegin() < p)
        //     break;
        // ll c2 = *ind['C' - 'A'].rbegin();
        // ind['C' - 'A'].erase(*ind['C' - 'A'].rbegin());
        // if (!(i < c1 && c1 < p && p < c2))
        //     break;
        icp.push_back({ i, c1, p });
    }
    ll hi = icp.size(), lo = 1, ans = 0;
    while (hi >= lo) {
        ll mid = lo + (hi - lo) / 2;
        bool isOk = true;
        vector<bool> vis(n, false);
        vector<array<int, 3>> tmp;
        for (int i = 0; i < mid; i++) {
            tmp.push_back(icp[i]);
            for (auto& it : icp[i])
                vis[it] = true;
        }
        for (int i = mid - 1, j = n - 1; i >= 0; i--) {
            while (j >= 0 && (vis[j] || a[j] != 'C'))
                j--;
            if (j < 0 || j < tmp[i][2]) {
                isOk = false;
                break;
            }
            vis[j] = true;
        }
        if (isOk)
            ans = mid, lo = mid + 1;
        else
            hi = mid - 1;
    }
    cout << ans << '\n';
    {
        ll mid = ans;
        vector<bool> vis(n, false);
        vector<array<int, 3>> tmp;
        for (int i = 0; i < mid; i++) {
            tmp.push_back(icp[i]);
            for (auto& it : icp[i])
                vis[it] = true;
        }
        for (int i = mid - 1, j = n - 1; i >= 0; i--) {
            while (j >= 0 && (vis[j] || a[j] != 'C'))
                j--;
            if (j < 0 || j < tmp[i][2]) {
                break;
            }
            vis[j] = true;
            cout << 1 + tmp[i][0] << " " << 1 + tmp[i][1] << " " << 1 + tmp[i][2] << " " << 1 + j << '\n';
        }
    }
}
 int32_t main()
{
    ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
    int t = 1;
    cin >> t;
    for (int i = 1; i <= t; i++) {
        Solve();
    }
    return 0;
}
// Coded by Tahsin Arafat (@TahsinArafat)