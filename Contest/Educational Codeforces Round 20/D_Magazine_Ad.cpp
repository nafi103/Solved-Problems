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
int n;
 bool check(int target, const vector<int> &arr){
    int cnt = 0, rem = 0;
    for(auto &x: arr){
        if(rem < x){
            rem = target;
            cnt++;
        }
        rem -= x;
    }
    return cnt <= n;
}
 void solve()
{
    cin >> n;
    vector<string> arr;
    string str;
    while(cin >> str){
        arr.push_back(str);
    }
    vector<int> words;
    for(auto &s: arr){
        int cnt = 0;
        for(auto &c: s){
            cnt++;
            if(c == '-'){
                words.push_back(cnt);
                cnt = 0;
            }
        }
        words.push_back(cnt + 1);
    }
    words.back()--;
     int l = *max_element(all(words)), r = accumulate(all(words), 0ll);
    while(l <= r){
        int mid = (l + r) / 2;
        if(check(mid, words))
            r = mid - 1;
        else
            l = mid + 1;
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