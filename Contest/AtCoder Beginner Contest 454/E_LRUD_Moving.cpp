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

bool flag = false;
char dir[] = {'U', 'L', 'R', 'D'};
int x[] = {-1, 0, 0, 1};
int y[] = {0, -1, 1, 0};

void solve()
{
    int n, a, b;
    cin >> n >> a >> b;
    if((n & 1) or (a + b) % 2 == 0){ 
        cout << "No" << endl;
        return;
    }
    cout << "Yes" << endl;
    string s1 = "", s2 = "";
    for(int i = 0; i < n / 2 - 1; i++){
        string tmp = string(n - 1, 'R') + 'D' + string(n - 1, 'L') + 'D';
        if(a > 2){
            s1 += tmp;
            a -= 2;
        }else{
            reverse(all(tmp));
            s2 = tmp + s2;
        }
    }
    for(int i = 0; i < n / 2 - 1; i++){
        string tmp = "DRUR";
        if(b > 2){
            s1 += tmp;
            b -= 2;
        }else{
            reverse(all(tmp));
            s2 = tmp + s2;
        }
    }
    if(a == 1){
        s1 += "DR";
    }else{
        s1 += "RD";
    }
    cout << s1 << s2 << endl;
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