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
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int n;
    cin >> n;
    pbds<pair<int,int>> d;
    vector<int> arr(n);
    map<int,int> cnt;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    for(int i = n - 1; i >= 0; i--){
        int x = arr[i];
        if(d.empty())
            arr[i] = 0;
        else{
            int pos = d.order_of_key({x, inf});
            int left = pos - cnt[x], right = sz(d) - pos;
            arr[i] = max(left, right);
        }
        d.insert({x, i});
        cnt[x]++;
    }
    for(int i = 0; i < n; i++){
        cout << arr[i] << (i == n - 1 ? '\n' : ' ');
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}