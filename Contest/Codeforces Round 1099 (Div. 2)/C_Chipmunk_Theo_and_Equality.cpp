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
    int n;
    cin >> n;
    vector<int> arr(n);
    vector<pair<int,int>> steps;
     for(int i = 0; i < n; i++){
        cin >> arr[i];
        int x = arr[i];
        vector<int> tmp;
        while(find(all(tmp), x) == tmp.end()){
            steps.push_back({x, sz(tmp)});
            tmp.push_back(x);
            if(x & 1)
                x++;
            else
                x /= 2;
        }
    }
     sort(all(steps));
    int p = 0, ans = inf, m = sz(steps);
    while(p < m){
        auto [curr, total] = steps[p];
        p++;
        int cnt = 1;
        while(p < m and steps[p].first == curr){
            total += steps[p].second;
            cnt++;
            p++;
        }
         if(cnt == n){
            ans = min(ans, total);
        }
    }
     cout << ans << endl;
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