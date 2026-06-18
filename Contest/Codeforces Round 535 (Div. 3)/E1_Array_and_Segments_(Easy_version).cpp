#include <bits/stdc++.h>
 using namespace std;
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
    int n, m, id = -1;
    cin >> n >> m;
    vector<int> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i];
    }
    int ans = *max_element(all(arr)) - *min_element(all(arr));
     vector<pair<int,int>> seg(m);
    for(auto &[l, r]: seg){
        cin >> l >> r;
        l--, r--;
    }
     for(int i = 0; i < n; i++){
        vector<int> parr(n, 0);
        for(auto &[l, r]: seg){
            if(l <= i and r >= i){
                parr[l]--;
                if(r + 1 < n)
                    parr[r + 1]++;
            }
        }
         for(int j = 1; j < n; j++){
            parr[j] += parr[j - 1];
        }
         int mx = -inf, mn = inf;
        for(int j = 0; j < n; j++){
            mx = max(mx, arr[j] + parr[j]);
            mn = min(mn, arr[j] + parr[j]);
        }
         if(mx - mn > ans){
            id = i;
            ans = mx - mn;
        }
    }
     if(id == -1){
        cout << ans << endl;
        cout << 0 << endl;
        return;
    }
     cout << ans << endl;
    vector<int> take;
    for(int i = 0; i < m; i++){
        auto &[l, r] = seg[i];
        if(l <= id and r >= id){
            take.push_back(i + 1);
        }
    }
    cout << sz(take) << endl;
    for(auto &x: take){
        cout << x << " ";
    }
    cout << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
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