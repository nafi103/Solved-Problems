#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


void solve()
{
    int n; cin >> n;
    vector<long long> a(n), b(n);
    unordered_map<long long,int> cntA, tot;
    cntA.reserve(2*n); tot.reserve(2*n);
    long long mn = LLONG_MAX;

    for (auto &x : a) {
        cin >> x;
        ++cntA[x];
        ++tot[x];
        mn = min(mn, x);
    }
    for (auto &x : b) {
        cin >> x;
        ++tot[x];
        mn = min(mn, x);
    }

    for (auto &kv : tot) {
        if (kv.second & 1) {
            cout << -1 << '\n';
            return;
        }
    }

    vector<pair<long long,int>> extraA, extraB;
    extraA.reserve(n);
    extraB.reserve(n);
    extraA.clear(); extraB.clear();

    for (auto &kv : tot) {
        long long val = kv.first;
        int target = kv.second / 2;
        int ca = cntA[val];
        if (ca > target) extraA.emplace_back(val, ca - target);
        else if (ca < target) extraB.emplace_back(val, target - ca);
    }

    sort(extraA.rbegin(), extraA.rend());
    sort(extraB.begin(), extraB.end());

    long long ans = 0;
    size_t i = 0, j = 0;
    while (i < extraA.size() && j < extraB.size()) {
        int k = min(extraA[i].second, extraB[j].second);
        long long costPer = min({ extraA[i].first, extraB[j].first, 2*mn });
        ans += costPer * k;
        extraA[i].second -= k;
        extraB[j].second -= k;
        if (extraA[i].second == 0) ++i;
        if (extraB[j].second == 0) ++j;
    }

    cout << ans << '\n';
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}