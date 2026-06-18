#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'
 void solve()
{
    int x = 0, y = 0;
    int n;
    char a;
    bool flag = false;
    cin >> n;
    for (int i = 0; i < n; i++)
    {
        cin >> a;
        if (a == 'U')
            y++;
        else if (a == 'D')
            y--;
        else if (a == 'L')
            x--;
        else
            x++;
        if (x == 1 && y == 1)
            flag = true;
    }
    if (flag)
        cout << "YES" << endl;
    else
        cout << "NO" << endl;
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}