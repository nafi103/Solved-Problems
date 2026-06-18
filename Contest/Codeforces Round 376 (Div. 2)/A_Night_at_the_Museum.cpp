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
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 int checkDis(char x, char y)
{
    int a = x - y;
    int b;
    if (a > 0)
        b = 26 - a;
    else
        b = 26 + a;
    return min(abs(a), abs(b));
}
 int main()
{
    fastIO;
    int ans = 0;
    string str;
    cin >> str;
    ans += checkDis(str[0], 'a');
    for (int i = 0; i < str.size() - 1; i++)
    {
        ans += checkDis(str[i], str[i + 1]);
    }
    cout << ans << "\n";
}