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

bool check(int &n, int &k, int median, vector<vector<int>> &grid){
    vector<vector<int>> pref(n + 1, vector<int>(n + 1, 0));
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= n; j++){
            pref[i][j] = (grid[i][j] <= median);
            pref[i][j] += pref[i - 1][j] + pref[i][j - 1] - pref[i - 1][j - 1];
        }
    }
    for(int i = k; i <= n; i++){
        for(int j = k; j <= n; j++){
            int ui = i - k + 1, uj = j - k + 1;
            int pref_sum = pref[i][j] - pref[ui - 1][j] - pref[i][uj - 1] + pref[ui - 1][uj - 1];
            if(pref_sum >= (k * k + 1) / 2)
                return true;
        }
    }
    return false;
}

void solve()
{
    int n, k, mx = -inf;
    cin >> n >> k;
    vector<vector<int>> grid(n + 1,vector<int>(n + 1)), id = grid;
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= n; j++){
            cin >> grid[i][j];
            mx = max(mx, grid[i][j]);
        }
    }

    int l = 0, r = mx;
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(n, k, mid, grid)){
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }
    cout << l << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}