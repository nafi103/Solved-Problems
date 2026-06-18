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
const int N = 2005;
int n;
vector<pair<int,int>> seg(N);
const pair<int,int> dummy = {-1, -1};
 void input(){
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> seg[i].first >> seg[i].second;
    }
    sort(seg.begin(), seg.begin() + n, [&](pair<int,int> &a, pair<int,int> &b){
        if(a.second != b.second)
            return a.second < b.second;
        return a.first < b.first;
    });
}
 void solve()
{
    input();
    int last = -1, ans = 0;
    pair<int,int> prev = dummy;
    for(int i = 0; i < n; i++){
        if(prev == dummy){
            if(seg[i].first > last)
                prev = seg[i];
            else
                ans++;
        }else{
            if(seg[i].first <= prev.second and seg[i].first > last){
                prev = dummy;
                last = seg[i].second;
            }else{
                if(seg[i].first > last)
                    prev = seg[i];
                ans++;
            }
        }
    }
    if(prev != dummy)
        ans++;
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