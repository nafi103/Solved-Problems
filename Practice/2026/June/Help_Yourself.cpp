#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

// #ifndef ONLINE_JUDGE
// #include "debug.h"
// #define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
// #else
// #define debug(...)
// #endif

/****************************************************************/

int expo(int base, int exp){
    int res = 1;
    while(exp){
        if(exp & 1)
            res = (res * base) % mod;
        base = (base * base) % mod;
        exp >>= 1;
    }
    return res;
}

void solve()
{
    int n;
    cin >> n;

    pbds<pair<int,int>> d;
    vector<pair<int,int>> seg(n);

    for(auto &[l, r]: seg)
        cin >> l >> r;
    sort(all(seg));

    int res = 0;
    for(int i = 0; i < n; i++){
        auto &[l, r] = seg[i];

        int not_intersect = d.order_of_key({l, -1});

        res = ((res * 2) % mod + expo(2, not_intersect)) % mod;
        d.insert({r, i});
    }

    cout << res << endl;
}

int32_t main()
{
    freopen("help.in", "r", stdin);
    freopen("help.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}