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
    int n, k, root_cnt = 0;
    cin >> n >> k;
    vector<pair<int,int>> arr(n);
    for(int i = 0; i < n; i++){
        cin >> arr[i].first;
        if(arr[i].first == 0)
            root_cnt++;
        arr[i].second = i;
    }
     if(root_cnt > 1 or root_cnt == 0){
        cout << -1 << endl;
        return;
    }
     sort(rbegin(arr), rend(arr));
    vector<pair<int,int>> prev_level, next_level;
    prev_level.push_back(arr.back());
    arr.pop_back();
    bool flag = true;
     vector<pair<int,int>> edges;
    while(!arr.empty()){
        debug(prev_level)
        next_level.clear();
        next_level.push_back(arr.back());
        arr.pop_back();
         while(!arr.empty() and arr.back().first == next_level.back().first){
            next_level.push_back(arr.back());
            arr.pop_back();
        }
        debug(next_level)
         if(next_level.back().first != prev_level.back().first + 1 or
            sz(prev_level) * k < sz(next_level)){
            cout << -1 << endl;
            return;
        }
         for(int i = 0, tk = k; i < sz(next_level); i++, tk--){
            if(tk == 0){
                tk = k;
                prev_level.pop_back();
            }
            edges.push_back({next_level[i].second, prev_level.back().second});
        }
         prev_level = next_level;
        if(flag){
            flag = false;
            k--;
        }
    }
     cout << n - 1 << endl;
    for(auto &[u, v]: edges){
        cout << u + 1 << ' ' << v + 1 << endl;
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
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}