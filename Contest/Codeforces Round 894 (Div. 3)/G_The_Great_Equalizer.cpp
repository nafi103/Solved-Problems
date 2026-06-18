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
 const int N = 2e5 + 10;
int arr[N];
 void out(int &x, map<int,int> &mp, set<int> &d, multiset<int> &gap){
 mp[x]--;
 if(mp[x] != 0)
  return;
 mp.erase(x);
 auto it = d.find(x);
 auto left = (it == d.begin() ? d.end() : prev(it));
 auto right = next(it);
 if(left != d.end())
  gap.erase(gap.find(x - *left));
 if(right != d.end())
  gap.erase(gap.find(*right - x));
 if(left != d.end() and right != d.end())
  gap.insert(*right - *left);
 d.erase(x);
}
 void in(int x, map<int,int> &mp, set<int> &d, multiset<int> &gap){
    if(mp[x]++){
        return;
    }
    auto it = d.lower_bound(x);
    auto right = it;
    auto left = (it == d.begin() ? d.end() : prev(it));
    if(left != d.end())
        gap.insert(x - *left);
    if(right != d.end())
        gap.insert(*right - x);
    if(left != d.end() && right != d.end())
        gap.erase(gap.find(*right - *left));
    d.insert(x);
}
 void solve()
{
    int n, id, val;
    cin >> n;
    map<int,int> mp;
    set<int> d;
    for(int i = 0; i < n; i++){
     cin >> arr[i];
     mp[arr[i]]++;
    }
    int last = -1;
    multiset<int> gap;
    for(auto &[f, s]: mp){
     if(last != -1){
      gap.insert(f - last);
     }
     last = f;
     d.insert(f);
    }
    int q;
    cin >> q;
    while(q--){
     cin >> id >> val;
     id--;
     out(arr[id], mp, d, gap);
     in(val, mp, d, gap);
     arr[id] = val;
     cout << (*mp.rbegin()).first + (sz(gap) ? (*gap.rbegin()) : 0ll) << " ";
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}