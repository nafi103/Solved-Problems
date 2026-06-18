#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 void solve()
{
    int n;
    cin >> n;
    vector<int> v(n);
    multiset<int> present;
    for(auto &x: v){
     cin >> x;
    }
    vector<int> last_index(n+1, -1);
    for(int i = n-1; i>=0; i--){
     if(last_index[v[i]] == -1)
      last_index[v[i]] = i;
    }
    vector<int> visited(n+1, false);
    vector<int> ans;
    int j = 0, i = 0, big = 1;
    present.insert(v[j]);
    while(i<n){
     while(j < n and (last_index[v[j]] != j or visited[v[j]])){
      j++;
      if(j < n and !visited[v[j]])
       present.insert(v[j]);
     }
     if(!present.empty() and big and v[i] == *present.rbegin()){
   ans.push_back(v[i]);
   present.erase(v[i]);
   big = big ^ 1;
   visited[v[i]] = true;
     }else if(!present.empty() and !big and v[i] == *present.begin()){
   ans.push_back(v[i]);
   present.erase(v[i]);
   big = big ^ 1;
   visited[v[i]] = true;
  }
     if(present.count(v[i])){
      present.erase(present.find(v[i]));
     }
     i++;
    }
    cout << sz(ans) << endl;
    for(auto &x: ans)
     cout<< x << " ";
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}