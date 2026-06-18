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
    int k;
    cin >> k;
    long long cur = 9, len = 1;
    while (k - cur * len > 0) {
        k -= cur * len;
        cur *= 10;
        len++;
    }
    string s = to_string(cur / 9 + (k - 1) / len);
    long long ans = 0;
    for (int i = 0; i < (k - 1) % len + 1; i++)
        ans += s[i] - '0';
    long long pr_s = 0;
    for (int i = 0; i < s.length(); i++) {
        int curd = s[i] - '0';
        if (curd)
            ans += curd * (len - 1) * cur / 2 + curd * (2 * pr_s + curd - 1) / 2 * cur / 9;
        cur /= 10, len--;
        pr_s += curd;
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