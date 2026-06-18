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
    vector<pair<int, char>> color(3);
    color[0].second = 'R', color[1].second = 'G', color[2].second = 'B';
    for(int i = 0; i < 3; i++){
        cin >> color[i].first;
    } 
    sort(all(color));
    string ans = "";
     //make second max and third max same
    while(color[0].first != color[1].first){
        ans.push_back(color[2].second);
        ans.push_back(color[1].second);
        color[2].first--, color[1].first--;
    }
     //alternating second max and third max
    int id = 0;
    while(color[1].first > 0 and color[2].first != color[1].first){
        ans.push_back(color[2].second);
        ans.push_back(color[id].second);
        color[2].first--, color[id].first--;
        id = id ^ 1;
    }
    if(color[0].first != color[1].first){
        id = id ^ 1;
        ans.pop_back();
        color[id].first++;
    }
     // all same
    string repeat_string = "XYZ";
    if(ans.empty())
        repeat_string = "RBG";
    else{
        set<char> s = {'R', 'G', 'B'};
        if(sz(ans) == 1){
            s.erase(ans.back());
            repeat_string[1] = ans.back();
            repeat_string[0] = *s.begin();
            s.erase(s.begin());
            repeat_string[2] = *s.begin();
        }else{
            int len = sz(ans);
            s.erase(ans[len - 1]);
            s.erase(ans[len - 2]);
            repeat_string[0] = ans[len - 2];
            repeat_string[1] = ans[len - 1];
            repeat_string[2] = *s.begin();
        }
    }
    while(color[2].first > 0 and color[0].first == color[1].first and color[1].first == color[2].first){
        ans += repeat_string;
        reverse(all(repeat_string));
        reverse(repeat_string.begin(), repeat_string.begin() + 2);
        color[0].first--, color[1].first--, color[2].first--;
    }
     //all didn't became same
    if(color[2].first){
        ans.push_back(color[2].second);
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