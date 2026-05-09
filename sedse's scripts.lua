-- ==========================================
-- 1. Load the Monolith Library (SedseUI)
-- ==========================================
local loadUrl = "https://raw.githubusercontent.com/SedseXD/SedseUI/refs/heads/main/Library.lua?t=" .. tostring(tick())
local Library, Notifications = loadstring(game:HttpGet(loadUrl))()

-- ==========================================
-- 2. CONFIGURATION & STATE
-- ==========================================
local CONFIG = {
    Enabled        = false,
    ActivationKey  = Enum.KeyCode.V,
    MaxTargetDist  = 15,
    BehindDistance = 5,
    WindupDelay    = 0.15,
    FlightDuration = 0.25,
    LockDuration   = 0.40,
    CurveStrength  = 10,
    ArchHeight     = 3,
    DashCooldown   = 0,
    BlackFlashDelay = 0.3, 
    AutoBlackFlash  = false, 
    AutoBlock       = false, 
    BlockLockOn     = false, 
    BlockDist       = 15,    
    BlockDuration   = 0.5,   
	AttackAnimIds  = {},
	Blacklist = { "Manji", "Supernova", "Shut", "Adapt", "Catching", "Splitter" },
}

local LOCK_CONFIG = {
    Enabled    = false,
    Method     = "Camera",
    TargetMode = "Closest",
    TargetPart = "HumanoidRootPart",
    SideOffset = 0,
    StickyTarget  = false,
}

local ESP_CONFIG = {
    Box      = { Enabled = false, Color = Color3.fromRGB(255, 255, 255) },
    Name     = { Enabled = false, Color = Color3.fromRGB(255, 255, 255) },
    Health   = { Enabled = false, Color = Color3.fromRGB(0,   255, 0)   },
    Distance = { Enabled = false, Color = Color3.fromRGB(200, 200, 200) },
    Tracer   = { Enabled = false, Color = Color3.fromRGB(255, 255, 255) },
    Item     = { Enabled = false, Color = Color3.fromRGB(255, 215, 0)   }
}

-- UI Mapping for Config System
local UI_Elements = {
    CONFIG = {},
    LOCK_CONFIG = {},
    ESP_CONFIG = { Box={}, Name={}, Health={}, Distance={}, Tracer={}, Item={} }
}

local isEnabled          = false
local isUnloaded         = false
local lastExecutionTime  = 0
local keybindConnection  = nil
local espConnection      = nil
local wasLockedBody      = false
local ESP_Cache          = {}
local ItemHighlights     = {}
local ItemTexts      = {}
local descendantAddedConn = nil
local descendantRemovingConn = nil
local comboInputConn = nil
local selectedGrabItem = ""

-- Services
local Players           = game:GetService("Players")
local UserInputService  = game:GetService("UserInputService")
local TweenService      = game:GetService("TweenService")
local RunService        = game:GetService("RunService")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local HttpService       = game:GetService("HttpService")
local CoreGui           = game:GetService("CoreGui")
local Camera            = workspace.CurrentCamera
local LocalPlayer       = Players.LocalPlayer
local mouse             = LocalPlayer:GetMouse()
local VIM = game:GetService("VirtualInputManager")
local PIANO_PATH = "RobloxPiano/Songs"

-- Piano State
local piano_st, piano_idx, piano_lt, piano_song, piano_fpath, piano_fmap = "Stopped", 1, 0, {}, "", {}
local piano_speed = 1.0
local piano_transpose = 0
local piano_looping = false

-- Ensure folders exist
if not isfolder("RobloxPiano") then makefolder("RobloxPiano") end
if not isfolder(PIANO_PATH) then makefolder(PIANO_PATH) end

-- Remotes
local BlockRemote = ReplicatedStorage:WaitForChild("Knit"):WaitForChild("Knit"):WaitForChild("Services"):WaitForChild("BlockService"):WaitForChild("RE"):WaitForChild("Activated")
local UnblockRemote = ReplicatedStorage:WaitForChild("Knit"):WaitForChild("Knit"):WaitForChild("Services"):WaitForChild("BlockService"):WaitForChild("RE"):WaitForChild("Deactivated")
local DivergentFistRemote = ReplicatedStorage:WaitForChild("Knit"):WaitForChild("Knit"):WaitForChild("Services"):WaitForChild("DivergentFistService"):WaitForChild("RE"):WaitForChild("Activated")
local ACTeleportRemote = ReplicatedStorage:WaitForChild("Knit"):WaitForChild("Knit"):WaitForChild("Services"):WaitForChild("AntiCheatService"):WaitForChild("RE"):WaitForChild("Teleport")

-- =======================================================
-- GLOBAL BLACKFLASH HOOK (Mobile Safe)
-- =======================================================
local isComboing = false 
local isAutoFiring = false 

local oldNamecall
local hookSuccess = pcall(function()
    oldNamecall = hookmetamethod(game, "__namecall", function(self, ...)
        if isUnloaded then return oldNamecall(self, ...) end
        local args = {...}
        local method = getnamecallmethod()
        if method == "FireServer" and self == DivergentFistRemote then
            if isComboing then return oldNamecall(self, ...) end
            if CONFIG.AutoBlackFlash and not isAutoFiring then
                local moveObject = args[1]
                local myChar = LocalPlayer.Character
                if moveObject and myChar and moveObject:IsDescendantOf(myChar) then
                    task.delay(CONFIG.BlackFlashDelay, function()
                        isAutoFiring = true 
                        DivergentFistRemote:FireServer(moveObject)
                        task.wait(0.1) 
                        isAutoFiring = false 
                    end)
                end
            end
        end
        return oldNamecall(self, ...)
    end)
end)

if not hookSuccess then
    warn("[SedseHub] hookmetamethod not supported on this executor. BlackFlash Hook disabled.")
end
-- =======================================================
-- 3. CORE LOGIC ENGINES
-- =======================================================
local function getBezierPoint(t, p0, p1, p2)
    return (1 - t)^2 * p0 + 2 * (1 - t) * t * p1 + t^2 * p2
end

local function getClosestTarget()
    local character = LocalPlayer.Character
    if not character then return nil end
    local root = character:FindFirstChild("HumanoidRootPart")
    if not root then return nil end
    local closestTarget, shortestDist = nil, CONFIG.MaxTargetDist
    
    for _, obj in ipairs(workspace:GetDescendants()) do
        if obj:IsA("Humanoid") and obj.Health > 0 then
            local tChar = obj.Parent
            if tChar and tChar ~= character then
                local tRoot = tChar:FindFirstChild("HumanoidRootPart") or tChar:FindFirstChild("Torso")
                if tRoot then
                    local d = (root.Position - tRoot.Position).Magnitude
                    if d < shortestDist then 
                        shortestDist = d 
                        closestTarget = tRoot 
                    end
                end
            end
        end
    end
    return closestTarget
end

-- MIDI Parser
local function parseMidi(data)
    local pos = 1
    local function rb() local b = string.byte(data, pos); pos = pos + 1; return b end
    local function rs(len) local s = string.sub(data, pos, pos + len - 1); pos = pos + len; return s end
    local function r16() return rb() * 256 + rb() end
    local function r32() return rb() * 16777216 + rb() * 65536 + rb() * 256 + rb() end
    local function rvlq()
        local v = 0
        while true do
            local b = rb()
            v = v * 128 + bit32.band(b, 0x7F)
            if bit32.band(b, 0x80) == 0 then break end
        end
        return v
    end
    if rs(4) ~= "MThd" then return {} end
    r32()
    local fmt, ntrk, div = r16(), r16(), r16()
    local evs = {}
    for i = 1, ntrk do
        if rs(4) ~= "MTrk" then break end
        local len = r32()
        local endp, tick, lst = pos + len, 0, 0
        while pos < endp do
            local d = rvlq()
            tick = tick + d
            local s = rb()
            if s < 0x80 then s = lst; pos = pos - 1 else lst = s end
            local et = bit32.rshift(s, 4)
            local ch = bit32.band(s, 0x0F)
            if s == 0xFF then
                local mt = rb()
                local ml = rvlq()
                local md = rs(ml)
                if mt == 0x51 and ml == 3 then
                    local mpqn = string.byte(md, 1) * 65536 + string.byte(md, 2) * 256 + string.byte(md, 3)
                    table.insert(evs, {tick = tick, type = "t", mpqn = mpqn})
                end
            elseif et == 0x9 and ch ~= 9 then
                local n, v = rb(), rb()
                if v > 0 then table.insert(evs, {tick = tick, type = "n", note = n}) end
            elseif et == 0x8 or et == 0xA or et == 0xB or et == 0xE then rb() rb()
            elseif et == 0xC or et == 0xD then rb() end
        end
        pos = endp
    end
    table.sort(evs, function(a, b) return a.tick < b.tick end)
    local res, curt, curtm, mpqn = {}, 0, 0, 500000
    for _, e in ipairs(evs) do
        local dt = e.tick - curt
        if dt > 0 then
            curtm = curtm + (dt / div) * (mpqn / 1000000)
            curt = e.tick
        end
        if e.type == "t" then mpqn = e.mpqn
        elseif e.type == "n" then table.insert(res, {time = curtm, note = e.note}) end
    end
    return res
end

local piano_nm = {
    [60]="1",[62]="2",[64]="3",[65]="4",[67]="5",[69]="6",[71]="7",[72]="8",[74]="9",[76]="0",
    [77]="q",[79]="w",[81]="e",[83]="r",[84]="t",[86]="y",[88]="u",[89]="i",[91]="o",[93]="p",
    [95]="a",[96]="s",[98]="d",[100]="f",[102]="g",[103]="h",[105]="j",[107]="k",[108]="l",
    [110]="z",[112]="x",[114]="c",[115]="v",[117]="b",[119]="n",[121]="m",
    [61]="!",[63]="@",[66]="$",[68]="%",[70]="^",[73]="*",[75]="(",
    [78]="Q",[80]="W",[82]="E",[85]="T",[87]="Y",[90]="I",[92]="O",
    [94]="P",[97]="S",[99]="D",[101]="G",[104]="H",[106]="J",[109]="L",
    [111]="Z",[113]="C",[116]="V",[118]="B"
}

local piano_km = {
    ["1"]=Enum.KeyCode.One,["2"]=Enum.KeyCode.Two,["3"]=Enum.KeyCode.Three,["4"]=Enum.KeyCode.Four,["5"]=Enum.KeyCode.Five,["6"]=Enum.KeyCode.Six,["7"]=Enum.KeyCode.Seven,["8"]=Enum.KeyCode.Eight,["9"]=Enum.KeyCode.Nine,["0"]=Enum.KeyCode.Zero,
    ["q"]=Enum.KeyCode.Q,["w"]=Enum.KeyCode.W,["e"]=Enum.KeyCode.E,["r"]=Enum.KeyCode.R,["t"]=Enum.KeyCode.T,["y"]=Enum.KeyCode.Y,["u"]=Enum.KeyCode.U,["i"]=Enum.KeyCode.I,["o"]=Enum.KeyCode.O,["p"]=Enum.KeyCode.P,
    ["a"]=Enum.KeyCode.A,["s"]=Enum.KeyCode.S,["d"]=Enum.KeyCode.D,["f"]=Enum.KeyCode.F,["g"]=Enum.KeyCode.G,["h"]=Enum.KeyCode.H,["j"]=Enum.KeyCode.J,["k"]=Enum.KeyCode.K,["l"]=Enum.KeyCode.L,["z"]=Enum.KeyCode.Z,["x"]=Enum.KeyCode.X,["c"]=Enum.KeyCode.C,["v"]=Enum.KeyCode.V,["b"]=Enum.KeyCode.B,["n"]=Enum.KeyCode.N,["m"]=Enum.KeyCode.M,
    ["!"]=Enum.KeyCode.One,["@"]=Enum.KeyCode.Two,["$"]=Enum.KeyCode.Four,["%"]=Enum.KeyCode.Five,["^"]=Enum.KeyCode.Six,["*"]=Enum.KeyCode.Eight,["("]=Enum.KeyCode.Nine,
    ["Q"]=Enum.KeyCode.Q,["W"]=Enum.KeyCode.W,["E"]=Enum.KeyCode.E,["T"]=Enum.KeyCode.T,["Y"]=Enum.KeyCode.Y,["I"]=Enum.KeyCode.I,["O"]=Enum.KeyCode.O,["P"]=Enum.KeyCode.P,["S"]=Enum.KeyCode.S,["D"]=Enum.KeyCode.D,["G"]=Enum.KeyCode.G,["H"]=Enum.KeyCode.H,["J"]=Enum.KeyCode.J,["L"]=Enum.KeyCode.L,["Z"]=Enum.KeyCode.Z,["C"]=Enum.KeyCode.C,["V"]=Enum.KeyCode.V,["B"]=Enum.KeyCode.B
}

local function piano_isShift(k)
    return k:match("^[A-Z]$") or k:match("^[!@$%%^*(]$")
end

local function piano_playChord(ks)
    local un, sh = {}, {}
    for _, k in ipairs(ks) do
        local c = piano_km[k]
        if c then
            if piano_isShift(k) then table.insert(sh, c) else table.insert(un, c) end
        end
    end
    task.spawn(function()
        if #un > 0 then
            for _, c in ipairs(un) do VIM:SendKeyEvent(true, c, false, game) end
            task.wait(0.02)
            for _, c in ipairs(un) do VIM:SendKeyEvent(false, c, false, game) end
        end
        if #sh > 0 then
            VIM:SendKeyEvent(true, Enum.KeyCode.LeftShift, false, game)
            task.wait(0.01)
            for _, c in ipairs(sh) do VIM:SendKeyEvent(true, c, false, game) end
            task.wait(0.02)
            for _, c in ipairs(sh) do VIM:SendKeyEvent(false, c, false, game) end
            VIM:SendKeyEvent(false, Enum.KeyCode.LeftShift, false, game)
        end
    end)
end

local function fireDivergentStrike(character)
    local moveset = character:FindFirstChild("Moveset")
    if moveset then
        local move = moveset:FindFirstChild("Divergent Fist")
        if move then 
            DivergentFistRemote:FireServer(move) 
        end
    end
end

-- FIXED: This function was the cause of the script not executing
local function executePlantedLock(root, target, humanoid)
    local lockStartTime = tick()
    local plantedPosition = root.Position
    
    local lockConn
    lockConn = RunService.Heartbeat:Connect(function()
        if tick() - lockStartTime > CONFIG.LockDuration then
            lockConn:Disconnect()
            if root then root.AssemblyLinearVelocity = Vector3.zero end
            if humanoid then humanoid.AutoRotate = true end
        else
            if root and target then
                root.AssemblyLinearVelocity = Vector3.zero
                root.CFrame = CFrame.new(plantedPosition, Vector3.new(target.Position.X, plantedPosition.Y, target.Position.Z))
            else
                lockConn:Disconnect()
                if humanoid then humanoid.AutoRotate = true end
            end
        end
    end)
end

local function executeSmoothArchCombo()
    if isUnloaded then return end
    local character = LocalPlayer.Character
    if not character then return end
    local root = character:FindFirstChild("HumanoidRootPart")
    local humanoid = character:FindFirstChildOfClass("Humanoid")
    if not root or not humanoid then return end
    
    local target = getClosestTarget()
    if not target then 
        notify("No target in range! (Max: " .. CONFIG.MaxTargetDist .. " studs)", "Warning")
        return 
    end
    
    if tick() - lastExecutionTime < CONFIG.DashCooldown then 
        notify("Dash is on cooldown!", "Warning")
        return 
    end
    
    lastExecutionTime = tick()

    local p0 = root.Position
    local offsetToPlayer = p0 - target.Position
    local isDashLeft = target.CFrame.RightVector:Dot(offsetToPlayer) > 0
    local isBehind = target.CFrame.LookVector:Dot(offsetToPlayer.Unit) < -0.1
    local isOptimalRange = offsetToPlayer.Magnitude <= (CONFIG.BehindDistance + 1.5)

    isComboing = true
    
    fireDivergentStrike(character)
    task.delay(CONFIG.BlackFlashDelay, function() 
        fireDivergentStrike(character) 
    end)

    if isBehind and isOptimalRange then
        humanoid.AutoRotate = false
        task.wait(CONFIG.BlackFlashDelay)
        executePlantedLock(root, target, humanoid)
        isComboing = false
        return
    end

    task.wait(CONFIG.WindupDelay)
    humanoid.AutoRotate = false
    humanoid:ChangeState(Enum.HumanoidStateType.Physics)

    local progress = Instance.new("NumberValue")
    progress.Value = 0
    local tween = TweenService:Create(progress, TweenInfo.new(CONFIG.FlightDuration, Enum.EasingStyle.Sine, Enum.EasingDirection.Out), {Value = 1})
    local conn = progress.Changed:Connect(function(val)
        if not target or not root then return end
        local dynP2 = (target.CFrame * CFrame.new(0, 0, CONFIG.BehindDistance)).Position
        local pathDir = (dynP2 - p0).Unit
        local swoopDir = isDashLeft and Vector3.new(0,1,0):Cross(pathDir).Unit or pathDir:Cross(Vector3.new(0,1,0)).Unit
        local dynP1 = ((p0 + dynP2) / 2) + Vector3.new(0, CONFIG.ArchHeight, 0) + (swoopDir * (isBehind and 0 or CONFIG.CurveStrength))
        root.CFrame = CFrame.new(getBezierPoint(val, p0, dynP1, dynP2), target.Position)
    end)
    
    tween:Play()
    tween.Completed:Connect(function()
        conn:Disconnect(); progress:Destroy()
        if not root or not target then
            if humanoid then humanoid.AutoRotate = true humanoid:ChangeState(Enum.HumanoidStateType.GettingUp) end
            isComboing = false
            return
        end
        humanoid:ChangeState(Enum.HumanoidStateType.Running)
        executePlantedLock(root, target, humanoid)
        task.wait(0.1)
        isComboing = false
    end)
end

local CurrentLockTarget = nil
local LockBodyGyro = nil
local lastSearchTime = 0

local function getLockTarget()
    if tick() - lastSearchTime < 0.5 then return nil end
    lastSearchTime = tick()

    local localChar = LocalPlayer.Character
    if not localChar then return nil end
    local localRoot = localChar:FindFirstChild("HumanoidRootPart")
    if not localRoot then return nil end
    
    local bestTarget, shortestDist = nil, math.huge

    for _, obj in ipairs(workspace:GetDescendants()) do
        if obj:IsA("Humanoid") and obj.Health > 0 then
            local tChar = obj.Parent
            if tChar and tChar ~= localChar then
                local tRoot = tChar:FindFirstChild("HumanoidRootPart") or tChar:FindFirstChild("Torso")
                if tRoot then
                    if LOCK_CONFIG.TargetMode == "Closest" then
                        local d = (localRoot.Position - tRoot.Position).Magnitude
                        if d < shortestDist then shortestDist = d; bestTarget = tChar end
                    elseif LOCK_CONFIG.TargetMode == "Closest to Mouse" then
                        local pos, onScreen = Camera:WorldToViewportPoint(tRoot.Position)
                        if onScreen then
                            local d = (Vector2.new(mouse.X, mouse.Y) - Vector2.new(pos.X, pos.Y)).Magnitude
                            if d < shortestDist then shortestDist = d; bestTarget = tChar end
                        end
                    end
                end
            end
        end
    end
    return bestTarget
end

RunService:BindToRenderStep("MonolithTargetLock", Enum.RenderPriority.Camera.Value + 1, function()
    if isUnloaded then return end
    local localChar = LocalPlayer.Character
    local humanoid = localChar and localChar:FindFirstChildOfClass("Humanoid")
    local localRoot = localChar and localChar:FindFirstChild("HumanoidRootPart")

    if not LOCK_CONFIG.Enabled then
        CurrentLockTarget = nil
        if wasLockedBody then 
            if humanoid then humanoid.AutoRotate = true end
            if LockBodyGyro then LockBodyGyro:Destroy(); LockBodyGyro = nil end
            wasLockedBody = false 
        end
        return
    end

    if LOCK_CONFIG.StickyTarget and CurrentLockTarget then
        local eHum = CurrentLockTarget:FindFirstChildOfClass("Humanoid")
        if not (CurrentLockTarget.Parent and eHum and eHum.Health > 0) then
            CurrentLockTarget = nil
        end
    end

    if not CurrentLockTarget then CurrentLockTarget = getLockTarget() end
    if not CurrentLockTarget or not localRoot or not humanoid then return end

    local targetPart = CurrentLockTarget:FindFirstChild(LOCK_CONFIG.TargetPart) or CurrentLockTarget:FindFirstChild("HumanoidRootPart")
    if not targetPart then return end

    if LOCK_CONFIG.Method == "Camera" then
        if wasLockedBody then 
            humanoid.AutoRotate = true 
            if LockBodyGyro then LockBodyGyro:Destroy(); LockBodyGyro = nil end
            wasLockedBody = false 
        end
        local targetPos = targetPart.Position + (Camera.CFrame.RightVector * LOCK_CONFIG.SideOffset)
        local targetCFrame = CFrame.lookAt(Camera.CFrame.Position, targetPos)
        Camera.CFrame = Camera.CFrame:Lerp(targetCFrame, 0.4) 
    elseif LOCK_CONFIG.Method == "Body" then
        humanoid.AutoRotate = false
        wasLockedBody = true
        if not LockBodyGyro or LockBodyGyro.Parent ~= localRoot then
            if LockBodyGyro then LockBodyGyro:Destroy() end
            LockBodyGyro = Instance.new("BodyGyro")
            LockBodyGyro.MaxTorque = Vector3.new(0, 400000, 0)
            LockBodyGyro.P = 50000; LockBodyGyro.D = 500; LockBodyGyro.Parent = localRoot
        end
        LockBodyGyro.CFrame = CFrame.lookAt(localRoot.Position, Vector3.new(targetPart.Position.X, localRoot.Position.Y, targetPart.Position.Z))
    end
end)

local function validatePosition(duration)
    task.spawn(function()
        local start = tick()
        while tick() - start < (duration or 0.5) do
            pcall(function()
                ACTeleportRemote:FireServer(tick())
            end)
            task.wait(0.05)
        end
    end)
end

-- =======================================================
-- 4. ESP ENGINE
-- =======================================================
local function CreateESP(player)
    -- Check if Drawing library exists before using it
    if not Drawing then 
        warn("[SedseHub] Drawing library not supported. ESP disabled.")
        return 
    end

local function RemoveESP(player)
    if ESP_Cache[player] then
        for _, obj in pairs(ESP_Cache[player]) do
            obj:Remove()
        end
        ESP_Cache[player] = nil
    end
end

    local esp = { Box = Drawing.new("Square"), Tracer = Drawing.new("Line"), Name = Drawing.new("Text"), Distance = Drawing.new("Text"), Health = Drawing.new("Text") }
    esp.Box.Thickness = 1.5; esp.Box.Filled = false; esp.Tracer.Thickness = 1.5
    for _, t in pairs({esp.Name, esp.Distance, esp.H}) do t.Size = 16; t.Center = true; t.Outline = true end
    ESP_Cache[player] = esp
end
for _, p in pairs(Players:GetPlayers()) do if p ~= LocalPlayer then CreateESP(p) end end
Players.PlayerAdded:Connect(CreateESP)
Players.PlayerRemoving:Connect(RemoveESP)

espConnection = RunService.RenderStepped:Connect(function()
    if isUnloaded then return end
    local CurrentCamera = workspace.CurrentCamera
    if not CurrentCamera then return end
    
    local itemsFolder = workspace:FindFirstChild("Items")
    for item, hl in pairs(ItemHighlights) do if not item or not item.Parent then hl:Destroy(); ItemHighlights[item] = nil end end
    for item, txt in pairs(ItemTexts) do if not item or not item.Parent then txt:Remove(); ItemTexts[item] = nil end end

    if ESP_CONFIG.Item.Enabled and itemsFolder then
        for _, item in pairs(itemsFolder:GetChildren()) do
            if not ItemHighlights[item] then
                local hl = Instance.new("Highlight"); hl.FillColor = ESP_CONFIG.Item.Color; hl.Parent = item; ItemHighlights[item] = hl
            end
            if not ItemTexts[item] then
                local txt = Drawing.new("Text"); txt.Size = 16; txt.Center = true; txt.Outline = true; txt.Color = Color3.new(1, 1, 1); txt.Text = item.Name; ItemTexts[item] = txt
            end
            local itemPos = item:IsA("Model") and item:GetPivot().Position or (item:IsA("BasePart") and item.Position)
            if itemPos then
                local screenPos, onScreen = CurrentCamera:WorldToScreenPoint(itemPos)
                if onScreen then ItemTexts[item].Visible = true; ItemTexts[item].Position = Vector2.new(screenPos.X, screenPos.Y - 25) else ItemTexts[item].Visible = false end
            end
        end
    else
        for item, hl in pairs(ItemHighlights) do hl:Destroy() end; ItemHighlights = {}
        for item, txt in pairs(ItemTexts) do txt:Remove() end; ItemTexts = {}
    end

    for player, esp in pairs(ESP_Cache) do
        local character = player.Character
        if character and character ~= LocalPlayer.Character then
            local root = character:FindFirstChild("HumanoidRootPart")
            local hum  = character:FindFirstChildOfClass("Humanoid")
            if root and hum and hum.Health > 0 then
                local pos, onScreen = CurrentCamera:WorldToScreenPoint(root.Position)
                if onScreen and pos.Z > 0 then
                    local distance = pos.Z
                    local height = (CurrentCamera.ViewportSize.Y / (2 * math.tan(math.rad(CurrentCamera.FieldOfView / 2)))) * (5 / distance)
                    local width = height * 0.6 
                    local boxX, boxY = pos.X - (width / 2), pos.Y - (height / 2)

                    esp.Box.Visible = ESP_CONFIG.Box.Enabled
                    if esp.Box.Visible then esp.Box.Size = Vector2.new(width, height); esp.Box.Position = Vector2.new(boxX, boxY); esp.Box.Color = ESP_CONFIG.Box.Color end
                    esp.Name.Visible = ESP_CONFIG.Name.Enabled
                    if esp.Name.Visible then esp.Name.Text = player.DisplayName; esp.Name.Position = Vector2.new(pos.X, boxY - 20); esp.Name.Color = ESP_CONFIG.Name.Color end
                    esp.Health.Visible = ESP_CONFIG.Health.Enabled
                    if esp.Health.Visible then esp.Health.Text = "["..math.floor(hum.Health).."]"; esp.Health.Position = Vector2.new(pos.X, boxY - 35); esp.Health.Color = ESP_CONFIG.Health.Color end
                    esp.Distance.Visible = ESP_CONFIG.Distance.Enabled
                    if esp.Distance.Visible then 
                        local myRoot = LocalPlayer.Character and LocalPlayer.Character:FindFirstChild("HumanoidRootPart")
                        local distStr = myRoot and math.floor((myRoot.Position - root.Position).Magnitude) or math.floor(distance)
                        esp.Distance.Text = distStr .. "s"; esp.Distance.Position = Vector2.new(pos.X, boxY + height + 5); esp.Distance.Color = ESP_CONFIG.Distance.Color 
                    end
                    esp.Tracer.Visible = ESP_CONFIG.Tracer.Enabled
                    if esp.Tracer.Visible then esp.Tracer.From = Vector2.new(CurrentCamera.ViewportSize.X / 2, CurrentCamera.ViewportSize.Y); esp.Tracer.To = Vector2.new(pos.X, pos.Y); esp.Tracer.Color = ESP_CONFIG.Tracer.Color end
                else
                    for _, k in pairs({"Box","Name","Health","Distance","Tracer"}) do esp[k].Visible = false end
                end
            else
                for _, k in pairs({"Box","Name","Health","Distance","Tracer"}) do esp[k].Visible = false end
            end
        else
            for _, k in pairs({"Box","Name","Health","Distance","Tracer"}) do esp[k].Visible = false end
        end
    end
end)

-- =======================================================
-- 5. HELPER SYSTEMS
-- =======================================================
local function notify(msg, nType)
    if Notifications and type(Notifications.create_notification) == "function" then
        Notifications:create_notification({ name = msg, type = nType or "Info", duration = 4 })
    else
        print("[SedseHub] " .. tostring(msg))
    end
end

local uiAccentColor, uiFontColor = Color3.fromRGB(100, 150, 255), Color3.fromRGB(240, 240, 240)
local function colorMatch(c1, c2) return math.abs(c1.R - c2.R) < 0.005 and math.abs(c1.G - c2.G) < 0.005 and math.abs(c1.B - c2.B) < 0.005 end

local _recolorThrottle = 0
local function recolorUI(oldColor, newColor)
    local now = tick()
    if now - _recolorThrottle < 0.04 then return end
    _recolorThrottle = now
    local ui = CoreGui:FindFirstChild("MonolithUI") or LocalPlayer.PlayerGui:FindFirstChild("MonolithUI")
    if not ui then return end
    for _, obj in pairs(ui:GetDescendants()) do
        if (obj:IsA("TextLabel") or obj:IsA("TextButton") or obj:IsA("TextBox")) and colorMatch(obj.TextColor3, oldColor) then obj.TextColor3 = newColor end
        if (obj:IsA("Frame") or obj:IsA("ImageLabel") or obj:IsA("TextButton")) and obj.BackgroundTransparency < 0.9 and colorMatch(obj.BackgroundColor3, oldColor) then obj.BackgroundColor3 = newColor end
    end
end

local FS_ROOT, FS_CONFIGS, FS_COMBOS = "SedseHub", "SedseHub/settings", "SedseHub/Combos"
local fsOK = (isfolder ~= nil and makefolder ~= nil and writefile ~= nil and readfile ~= nil and listfiles ~= nil and delfile ~= nil)
local function ensureFolders()
    if not isfolder(FS_ROOT) then makefolder(FS_ROOT) end
    if not isfolder(FS_CONFIGS) then makefolder(FS_CONFIGS) end
    if not isfolder(FS_COMBOS) then makefolder(FS_COMBOS) end
end

local function c3ToTbl(c) return { r = math.floor(c.R*255 + 0.5), g = math.floor(c.G*255 + 0.5), b = math.floor(c.B*255 + 0.5) } end
local function tblToC3(t) return Color3.fromRGB(t.r or 255, t.g or 255, t.b or 255) end

local function buildSnapshot()
    return {
        CONFIG = { Enabled = CONFIG.Enabled, MaxTargetDist = CONFIG.MaxTargetDist, BehindDistance = CONFIG.BehindDistance, WindupDelay = CONFIG.WindupDelay, FlightDuration = CONFIG.FlightDuration, LockDuration = CONFIG.LockDuration, CurveStrength = CONFIG.CurveStrength, ArchHeight = CONFIG.ArchHeight, DashCooldown = CONFIG.DashCooldown },
        LOCK_CONFIG = { Enabled = LOCK_CONFIG.Enabled, Method = LOCK_CONFIG.Method, TargetMode = LOCK_CONFIG.TargetMode, TargetPart = LOCK_CONFIG.TargetPart, SideOffset = LOCK_CONFIG.SideOffset, StickyTarget = LOCK_CONFIG.StickyTarget },
        ESP_CONFIG = { Box = { Enabled = ESP_CONFIG.Box.Enabled, Color = c3ToTbl(ESP_CONFIG.Box.Color) }, Name = { Enabled = ESP_CONFIG.Name.Enabled, Color = c3ToTbl(ESP_CONFIG.Name.Color) }, Health = { Enabled = ESP_CONFIG.Health.Enabled, Color = c3ToTbl(ESP_CONFIG.Health.Color) }, Distance = { Enabled = ESP_CONFIG.Distance.Enabled, Color = c3ToTbl(ESP_CONFIG.Distance.Color) }, Tracer = { Enabled = ESP_CONFIG.Tracer.Enabled, Color = c3ToTbl(ESP_CONFIG.Tracer.Color) }, Item = { Enabled = ESP_CONFIG.Item.Enabled, Color = c3ToTbl(ESP_CONFIG.Item.Color) } }
    }
end

local function applySnapshot(data)
    if data.CONFIG then for k, v in pairs(data.CONFIG) do if UI_Elements.CONFIG[k] and UI_Elements.CONFIG[k].set then UI_Elements.CONFIG[k]:set(v) end end end
    if data.LOCK_CONFIG then for k, v in pairs(data.LOCK_CONFIG) do if UI_Elements.LOCK_CONFIG[k] then if UI_Elements.LOCK_CONFIG[k].set_value then UI_Elements.LOCK_CONFIG[k]:set_value(v) elseif UI_Elements.LOCK_CONFIG[k].set then UI_Elements.LOCK_CONFIG[k]:set(v) end end end end
    if data.ESP_CONFIG then for key, val in pairs(data.ESP_CONFIG) do if UI_Elements.ESP_CONFIG[key] then if val.Enabled ~= nil and UI_Elements.ESP_CONFIG[key].Toggle then UI_Elements.ESP_CONFIG[key].Toggle:set(val.Enabled) end if val.Color and UI_Elements.ESP_CONFIG[key].Colorpicker then UI_Elements.ESP_CONFIG[key].Colorpicker:set(tblToC3(val.Color)) end end end end
end

local function getConfigNames()
    if not fsOK then return {} end
    ensureFolders()
    local ok, files = pcall(listfiles, FS_CONFIGS)
    if not ok then return {} end
    local names = {}
    for _, path in pairs(files) do local name = path:match("([^/\\]+)%.json$") if name then table.insert(names, name) end end
    table.sort(names)
    return names
end

local function fsSave(name, overwrite)
    if not fsOK or name == "" then return false, "Invalid name or no FS API" end
    ensureFolders()
    local path = FS_CONFIGS .. "/" .. name .. ".json"
    if not overwrite and isfile(path) then return false, "Exists - use Overwrite" end
    local ok, err = pcall(writefile, path, HttpService:JSONEncode(buildSnapshot()))
    return ok, ok and ('Saved "' .. name .. '"') or tostring(err)
end

local function fsLoad(name)
    if not fsOK or name == "" then return false, "Invalid name or no FS API" end
    local path = FS_CONFIGS .. "/" .. name .. ".json"
    if not isfile(path) then return false, "Not found" end
    local ok, content = pcall(readfile, path)
    if not ok then return false, "Read error" end
    local parsed, decoded = pcall(HttpService.JSONDecode, HttpService, content)
    if not parsed then return false, "JSON error" end
    local applied, applyErr = pcall(applySnapshot, decoded)
    return applied, applied and ('Loaded "' .. name .. '"') or tostring(applyErr)
end

local function fsDelete(name)
    if not fsOK or name == "" then return false, "Invalid name" end
    local path = FS_CONFIGS .. "/" .. name .. ".json"
    if not isfile(path) then return false, "Not found" end
    local ok, err = pcall(delfile, path)
    return ok, ok and ('Deleted "' .. name .. '"') or tostring(err)
end

-- =======================================================
-- AUTO-BLOCK ENGINE (XENON-INSPIRED PRECISION)
-- =======================================================
local isBlocking = false
local trackedAnimators = {} 
local debugAntiSpam = {}

local INSTA_BLOCK_IDS = {
    ["123456789"] = true, 
    ["987654321"] = true,
}

local SAFE_ANIM_KEYWORDS = {
    "idle", "walk", "run", "jump", "fall", "land", "climb", "sit", "swim", "emote", "dance", "block", "stun", "death", "ragdoll", "getup", "spawn",
    "hit", "hurt", "damage", "flinch", "knockback", "reaction", "hitstun", "recoil", "impact", "guard", "break", "recover",
}

local function isAnimSafe(animName)
    local lower = animName:lower()
    for _, keyword in pairs(SAFE_ANIM_KEYWORDS) do if string.find(lower, keyword) then return true end end
    return false
end

local blockLockConnection = nil
local function performBlock(attackerChar)
    if isBlocking then return end
    isBlocking = true
    BlockRemote:FireServer()
    if CONFIG.BlockLockOn and attackerChar then
        local localChar = LocalPlayer.Character
        local localRoot = localChar and localChar:FindFirstChild("HumanoidRootPart")
        local humanoid = localChar and localChar:FindFirstChildOfClass("Humanoid")
        local enemyRoot = attackerChar:FindFirstChild("HumanoidRootPart")
        if localRoot and humanoid and enemyRoot then
            humanoid.AutoRotate = false
            blockLockConnection = RunService.Heartbeat:Connect(function()
                if localRoot and enemyRoot and enemyRoot.Parent then
                    localRoot.CFrame = CFrame.lookAt(localRoot.Position, Vector3.new(enemyRoot.Position.X, localRoot.Position.Y, enemyRoot.Position.Z))
                end
            end)
        end
    end
    task.delay(CONFIG.BlockDuration, function()
        UnblockRemote:FireServer()
        if blockLockConnection then blockLockConnection:Disconnect(); blockLockConnection = nil end
        local humanoid = LocalPlayer.Character and LocalPlayer.Character:FindFirstChildOfClass("Humanoid")
        if humanoid then humanoid.AutoRotate = true end
        isBlocking = false
    end)
end

local function hookAnimator(character, animator)
    if trackedAnimators[animator] then return end 
    trackedAnimators[animator] = animator.AnimationPlayed:Connect(function(track)
        if not CONFIG.AutoBlock or isBlocking then return end
        
        local localChar = LocalPlayer.Character
        if not localChar or character:IsDescendantOf(localChar) then return end
        if Players:GetPlayerFromCharacter(character) == LocalPlayer then return end
        
        local localRoot = localChar:FindFirstChild("HumanoidRootPart")
        local enemyRoot = character:FindFirstChild("HumanoidRootPart")
        if not localRoot or not enemyRoot then return end
        if (localRoot.Position - enemyRoot.Position).Magnitude > CONFIG.BlockDist then return end
        
        local animId = track.Animation.AnimationId:match("%d+$")
        local animName = track.Name or ""

        if _G.DebugBlocker and not debugAntiSpam[animId] then
            debugAntiSpam[animId] = true
            print("[AutoBlock] '" .. character.Name .. "' played ID: " .. tostring(animId) .. " | Name: " .. animName)
            task.delay(2, function() debugAntiSpam[animId] = nil end)
        end

        if (animId and INSTA_BLOCK_IDS[animId]) or (not isAnimSafe(animName) and animId ~= "") then 
            performBlock(character) 
        end
    end)
end

task.spawn(function()
    for _, obj in pairs(workspace:GetDescendants()) do
        if obj:IsA("Humanoid") and obj.Parent ~= LocalPlayer.Character then
            local animator = obj:FindFirstChildOfClass("Animator")
            if animator then hookAnimator(obj.Parent, animator) end
        end
    end
end)

workspace.DescendantAdded:Connect(function(obj)
    if obj:IsA("Animator") then
        local hum = obj.Parent
        if hum and hum:IsA("Humanoid") and hum.Parent ~= LocalPlayer.Character then hookAnimator(hum.Parent, obj) end
    end
end)

workspace.DescendantRemoving:Connect(function(obj)
    if obj:IsA("Animator") then
        if trackedAnimators[obj] then trackedAnimators[obj]:Disconnect(); trackedAnimators[obj] = nil end
    end
end)

task.spawn(function()
    while true do
        if piano_st == "Playing" then
            if piano_idx > #piano_song then
                if piano_looping then
                    piano_idx, piano_lt = 1, 0
                else
                    piano_st, piano_idx, piano_lt = "Stopped", 1, 0
                end
            else
                local e = piano_song[piano_idx]
                local w = (e.time - piano_lt) / piano_speed
                if w > 0.001 then task.wait(w) end
                local window = math.max(0.01, 0.02 / piano_speed)
                local ck, j = {}, piano_idx
                while j <= #piano_song and (piano_song[j].time - e.time) <= window do
                    local note = piano_song[j].note + piano_transpose
                    local k = piano_nm[note]
                    if k then table.insert(ck, k) end
                    j = j + 1
                end
                if #ck > 0 then piano_playChord(ck) end
                piano_lt, piano_idx = e.time, j
            end
        else
            task.wait(0.1)
        end
        task.wait()
    end
end)

-- =======================================================
-- 6. UI INTEGRATION
-- =======================================================
pcall(function()
    local Window = Library:window({ Name = "Sedse JJS", Loading = true, Icon = "lucide:flame" })
    _G.ToggleMyMenu = function() Window.toggle_menu() end
    local MainTab = Window:Tab({ Name = "BlackFlash", Icon = "lucide:sparkles" })
    local BlockTab = Window:Tab({ Name = "Auto Block", Icon = "lucide:shield"})
	local MainSec = MainTab:Section({ Name = "Combo Config", side = "left" })
	local BlackFlashSec = MainTab:Section({ Name = "Black Flash", side = "right"})
	local BlockSec = BlockTab:Section({ Name = "Auto Block", side = "left"})

    UI_Elements.CONFIG.Enabled = MainSec:Toggle({ Name = "Auto BlackFlash Chain", default = false, Callback = function(V) isEnabled = V end })
    UI_Elements.CONFIG.AutoBlackFlash = BlackFlashSec:Toggle({ Name = "Auto Blackflash", default = false, Callback = function(V) CONFIG.AutoBlackFlash = V end })
    UI_Elements.CONFIG.BlackFlashChainKey = BlackFlashSec:Keybind({ Name = "BlackFlash Chain Key", default = CONFIG.ActivationKey, Callback = function(KeyCode) CONFIG.ActivationKey = KeyCode end})
    UI_Elements.CONFIG.BlackFlashDelay = BlackFlashSec:Slider({ Name = "Black Flash Delay", min = 0, max = 5, default = CONFIG.BlackFlashDelay, Callback = function(V) CONFIG.BlackFlashDelay = V end})
    UI_Elements.CONFIG.AutoBlock = BlockSec:Toggle({ Name = "Auto Block", default = false, Callback = function(V) CONFIG.AutoBlock = V end })
    UI_Elements.CONFIG.BlockLockOn = BlockSec:Toggle({ Name = "Block + Lock On", default = false, Callback = function(V) CONFIG.BlockLockOn = V end })
    UI_Elements.CONFIG.BlockDist = BlockSec:Slider({ Name = "Block Distance", min = 1, max = 30, default = CONFIG.BlockDist, Callback = function(V) CONFIG.BlockDist = V end })
    UI_Elements.CONFIG.BlockDuration = BlockSec:Slider({ Name = "Block Duration", min = 0.1, max = 2, default = CONFIG.BlockDuration, Callback = function(V) CONFIG.BlockDuration = V end })
    UI_Elements.CONFIG.MaxTargetDist = MainSec:Slider({ Name = "Search Radius",   min = 5,  max = 100, default = CONFIG.MaxTargetDist,  Callback = function(V) CONFIG.MaxTargetDist  = V end })
    UI_Elements.CONFIG.BehindDistance = MainSec:Slider({ Name = "Behind Distance", min = 1,  max = 15,  default = CONFIG.BehindDistance, Callback = function(V) CONFIG.BehindDistance = V end })
    UI_Elements.CONFIG.DashCooldown = MainSec:Slider({ Name = "Dash Cooldown",   min = 0,  max = 10,  default = CONFIG.DashCooldown,   Callback = function(V) CONFIG.DashCooldown = V end })
    
    MainSec:Button({ Name = "🔴  Unload Script", Callback = function()
        local ui = CoreGui:FindFirstChild("MonolithUI") or LocalPlayer.PlayerGui:FindFirstChild("MonolithUI")
        if ui then ui:Destroy() end
        if _G.UnloadComboHub then _G.UnloadComboHub() end
    end })

    local LockTab = Window:Tab({ Name = "Lock", Icon = "lucide:lock-keyhole" })
    local LockSec = LockTab:Section({ Name = "Target Lock", side = "left" })
    UI_Elements.LOCK_CONFIG.Enabled = LockSec:Toggle({ Name = "Enable Lock", default = false, Callback = function(V) LOCK_CONFIG.Enabled = V end })
    LockSec:Toggle({ Name = "Sticky Target (Until Dead)", default = false, Callback = function(V) LOCK_CONFIG.StickyTarget = V end })
    UI_Elements.LOCK_CONFIG.Method = LockSec:Dropdown({ Name = "Method", items = {"Camera", "Body"}, default = "Camera", Callback = function(V) LOCK_CONFIG.Method = V end })
    UI_Elements.LOCK_CONFIG.TargetMode = LockSec:Dropdown({ Name = "Target Mode", items = {"Closest", "Closest to Mouse"}, default = "Closest", Callback = function(V) LOCK_CONFIG.TargetMode = V end })
    UI_Elements.LOCK_CONFIG.TargetPart = LockSec:Dropdown({ Name = "Target Part", items = {"Head", "HumanoidRootPart"}, default = "HumanoidRootPart", Callback = function(V) LOCK_CONFIG.TargetPart = V end })
    UI_Elements.LOCK_CONFIG.SideOffset = LockSec:Slider({ Name = "Camera Side Offset", min = -8, max = 8, default = 0, Callback = function(V) LOCK_CONFIG.SideOffset = V end })

    local ComboTab = Window:Tab({ Name = "Combos", Icon = "lucide:swords" })
    local ComboSec = ComboTab:Section({ Name = "Combo Recorder", side = "left" })
    local ComboPlaySec = ComboTab:Section({ Name = "Playback", side = "right" })

    local function serializeCombo(inputs)
        local serialized = {}
        for _, inp in ipairs(inputs) do
            local entry = { type = inp.type, delay = inp.delay }
            if inp.keyCode then entry.keyCode = tostring(inp.keyCode):gsub("Enum.KeyCode.", "") end
            if inp.button then entry.button = inp.button end
            if inp.dirX then entry.dirX = inp.dirX end
            if inp.dirZ then entry.dirZ = inp.dirZ end
            table.insert(serialized, entry)
        end
        return serialized
    end

    local function deserializeCombo(serialized)
        local inputs = {}
        for _, entry in ipairs(serialized) do
            local inp = { type = entry.type, delay = entry.delay }
            if entry.keyCode then inp.keyCode = Enum.KeyCode[entry.keyCode] or Enum.KeyCode.Unknown end
            if entry.button then inp.button = entry.button end
            if entry.dirX then inp.dirX = entry.dirX end
            if entry.dirZ then inp.dirZ = entry.dirZ end
            table.insert(inputs, inp)
        end
        return inputs
    end

    local function saveComboFile(name, inputs)
        if not fsOK then return false, "No filesystem API" end
        ensureFolders()
        local path = FS_COMBOS .. "/" .. name .. ".json"
        local data = { name = name, inputs = serializeCombo(inputs) }
        local ok, err = pcall(writefile, path, HttpService:JSONEncode(data))
        return ok, ok and ("Saved " .. path) or tostring(err)
    end

    local function loadComboFile(name)
        if not fsOK then return nil end
        local path = FS_COMBOS .. "/" .. name .. ".json"
        if not isfile(path) then return nil end
        local ok, content = pcall(readfile, path)
        if not ok then return nil end
        local parsed, data = pcall(HttpService.JSONDecode, HttpService, content)
        if not parsed then return nil end
        return deserializeCombo(data.inputs)
    end

    local function loadAllCombos()
        local combos = {}
        if not fsOK then return combos end
        ensureFolders()
        local ok, files = pcall(listfiles, FS_COMBOS)
        if not ok then return combos end
        for _, path in pairs(files) do
            local name = path:match("([^/\\]+)%.json$")
            if name then
                local inputs = loadComboFile(name)
                if inputs then combos[name] = { inputs = inputs } end
            end
        end
        return combos
    end

    local function deleteComboFile(name)
        if not fsOK then return false end
        local path = FS_COMBOS .. "/" .. name .. ".json"
        if not isfile(path) then return false end
        pcall(delfile, path)
        return true
    end

    local savedCombos = loadAllCombos()
    local isRecording = false
    local currentRecording = {}
    local lastInputTime = 0
    local recordConnections = {}
    local comboDropdownRef = nil
    local comboNamesList = {}
    local comboInfoLabel = nil

    local function getComboNames()
        local names = {}
        for name, _ in pairs(savedCombos) do table.insert(names, name) end
        table.sort(names)
        return names
    end

    local function getInputName(input)
        if input.type == "key_down" or input.type == "key_up" then return tostring(input.keyCode):gsub("Enum.KeyCode.", "")
        elseif input.type == "mouse_down" or input.type == "mouse_up" then return input.button .. " Click"
        elseif input.type == "move_dir" then return "Move(" .. string.format("%.1f,%.1f", input.dirX, input.dirZ) .. ")" end
        return "?"
    end

    local function updateComboInfo(name)
        if not comboInfoLabel then return end
        local combo = savedCombos[name]
        if not combo then comboInfoLabel:set("No combo selected"); return end
        local inputs = combo.inputs
        local totalTime, keyCount, clickCount, moveCount = 0, 0, 0, 0
        local summary = {}
        for _, inp in ipairs(inputs) do
            totalTime = totalTime + (inp.delay or 0)
            if inp.type == "key_down" then keyCount = keyCount + 1; table.insert(summary, getInputName(inp))
            elseif inp.type == "mouse_down" then clickCount = clickCount + 1; table.insert(summary, inp.button)
            elseif inp.type == "move_dir" then moveCount = moveCount + 1 end
        end
        local seqStr = ""
        if #summary > 12 then
            for i = 1, 12 do seqStr = seqStr .. summary[i] .. " > " end
            seqStr = seqStr .. "... (+" .. (#summary - 12) .. " more)"
        else seqStr = table.concat(summary, " > ") end
        local info = string.format("📋 '%s'\nInputs: %d | Keys: %d | Clicks: %d | Moves: %d\nDuration: %.1fs\nSequence: %s", name, #inputs, keyCount, clickCount, moveCount, totalTime, seqStr)
        comboInfoLabel:set(info)
    end

    local function startRecording()
        if isRecording then return end
        isRecording = true
        currentRecording = {}
        lastInputTime = tick()
        notify("Recording...", "Info")
        local keyDownConn = UserInputService.InputBegan:Connect(function(input, gameProcessed)
            if not isRecording then return end
            if input.UserInputType == Enum.UserInputType.Keyboard then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "key_down", keyCode = input.KeyCode, delay = delay })
            elseif input.UserInputType == Enum.UserInputType.MouseButton1 then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "mouse_down", button = "Left", delay = delay })
            elseif input.UserInputType == Enum.UserInputType.MouseButton2 then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "mouse_down", button = "Right", delay = delay })
            end
        end)
        local keyUpConn = UserInputService.InputEnded:Connect(function(input)
            if not isRecording then return end
            if input.UserInputType == Enum.UserInputType.Keyboard then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "key_up", keyCode = input.KeyCode, delay = delay })
            elseif input.UserInputType == Enum.UserInputType.MouseButton1 then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "mouse_up", button = "Left", delay = delay })
            elseif input.UserInputType == Enum.UserInputType.MouseButton2 then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "mouse_up", button = "Right", delay = delay })
            end
        end)
        local lastMoveDir = Vector3.zero
        local moveConn = RunService.Heartbeat:Connect(function()
            if not isRecording then return end
            local char = LocalPlayer.Character
            if not char then return end
            local humanoid = char:FindFirstChildOfClass("Humanoid")
            if not humanoid then return end
            local moveDir = humanoid.MoveDirection
            if moveDir ~= lastMoveDir then
                local delay = tick() - lastInputTime; lastInputTime = tick()
                table.insert(currentRecording, { type = "move_dir", dirX = moveDir.X, dirZ = moveDir.Z, delay = delay })
                lastMoveDir = moveDir
            end
        end)
        table.insert(recordConnections, keyDownConn)
        table.insert(recordConnections, keyUpConn)
        table.insert(recordConnections, moveConn)
    end

    local function stopRecording(comboName)
        if not isRecording then return end
        isRecording = false
        for _, conn in pairs(recordConnections) do conn:Disconnect() end
        recordConnections = {}
        if #currentRecording == 0 then notify("No inputs recorded.", "Error"); return end
        local name = comboName or "Combo " .. tostring(#savedCombos + 1)
        savedCombos[name] = { inputs = currentRecording }
        local ok, err = saveComboFile(name, currentRecording)
        if not ok then notify("Disk Save Error: " .. tostring(err), "Warning") else notify("Saved '" .. name .. "'", "Success") end
        currentRecording = {}
        comboNamesList = getComboNames()
        if comboDropdownRef then comboDropdownRef:set(comboNamesList) end
        updateComboInfo(name)
    end

    local function playCombo(name)
        local combo = savedCombos[name]
        if not combo then notify("Combo not found!", "Error"); return end
        notify("Playing '" .. name .. "'...", "Info")
        task.spawn(function()
            local VIM_S = game:GetService("VirtualInputManager")
            local char = LocalPlayer.Character
            local humanoid = char and char:FindFirstChildOfClass("Humanoid")
            for i, input in ipairs(combo.inputs) do
                if input.delay and input.delay > 0.005 then task.wait(input.delay) end
                if input.type == "key_down" then VIM_S:SendKeyEvent(true, input.keyCode, false, game)
                elseif input.type == "key_up" then VIM_S:SendKeyEvent(false, input.keyCode, false, game)
                elseif input.type == "mouse_down" then
                    if input.button == "Left" then VIM_S:SendMouseButtonEvent(0, 0, 0, true, game, 0)
                    elseif input.button == "Right" then VIM_S:SendMouseButtonEvent(0, 0, 1, true, game, 0) end
                elseif input.type == "mouse_up" then
                    if input.button == "Left" then VIM_S:SendMouseButtonEvent(0, 0, 0, false, game, 0)
                    elseif input.button == "Right" then VIM_S:SendMouseButtonEvent(0, 0, 1, false, game, 0) end
                elseif input.type == "move_dir" then
                    if humanoid then
                        local dir = Vector3.new(input.dirX, 0, input.dirZ)
                        if dir.Magnitude > 0 then
                            local camCF = Camera.CFrame
                            local forward = camCF.LookVector * Vector3.new(1, 0, 1)
                            local right = camCF.RightVector * Vector3.new(1, 0, 1)
                            if forward.Magnitude > 0 then forward = forward.Unit end
                            if right.Magnitude > 0 then right = right.Unit end
                            local forwardDot, rightDot = dir:Dot(forward), dir:Dot(right)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.W, false, game)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.A, false, game)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.S, false, game)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.D, false, game)
                            if forwardDot > 0.3 then VIM_S:SendKeyEvent(true, Enum.KeyCode.W, false, game) end
                            if forwardDot < -0.3 then VIM_S:SendKeyEvent(true, Enum.KeyCode.S, false, game) end
                            if rightDot > 0.3 then VIM_S:SendKeyEvent(true, Enum.KeyCode.D, false, game) end
                            if rightDot < -0.3 then VIM_S:SendKeyEvent(true, Enum.KeyCode.A, false, game) end
                        else
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.W, false, game)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.A, false, game)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.S, false, game)
                            VIM_S:SendKeyEvent(false, Enum.KeyCode.D, false, game)
                        end
                    end
                end
            end
            VIM_S:SendKeyEvent(false, Enum.KeyCode.W, false, game)
            VIM_S:SendKeyEvent(false, Enum.KeyCode.A, false, game)
            VIM_S:SendKeyEvent(false, Enum.KeyCode.S, false, game)
            VIM_S:SendKeyEvent(false, Enum.KeyCode.D, false, game)
            notify("Combo '" .. name .. "' finished!", "Success")
        end)
    end

    local comboNameInput = ""
    ComboSec:Textbox({ Name = "Combo Name", Placeholder = "Enter combo name...", Callback = function(V) comboNameInput = V end })
    ComboSec:Button({ Name = "🔴  Start Recording (F2)", Callback = function() startRecording() end })
    ComboSec:Button({ Name = "⏹️  Stop & Save (F1)", Callback = function() stopRecording(comboNameInput ~= "" and comboNameInput or nil) end })

    comboInputConn = UserInputService.InputBegan:Connect(function(input, gameProcessed)
        if gameProcessed then return end
        if input.KeyCode == Enum.KeyCode.F2 then startRecording()
        elseif input.KeyCode == Enum.KeyCode.F1 then stopRecording(comboNameInput ~= "" and comboNameInput or nil) end
    end)

    local selectedCombo = ""
    comboNamesList = getComboNames()
    comboDropdownRef = ComboPlaySec:Dropdown({ Name = "Select Combo", items = comboNamesList, default = "", Callback = function(V) selectedCombo = V; updateComboInfo(V) end })
    ComboPlaySec:Button({ Name = "🔄  Refresh List", Callback = function() savedCombos = loadAllCombos(); comboNamesList = getComboNames(); if comboDropdownRef then comboDropdownRef:set(comboNamesList) end; notify("Combo list refreshed!", "Success") end })
    ComboPlaySec:Button({ Name = "▶️  Play Combo", Callback = function() if selectedCombo ~= "" then playCombo(selectedCombo) else notify("Select a combo first!", "Error") end end })
    ComboPlaySec:Button({ Name = "🗑️  Delete Combo", Callback = function()
        if selectedCombo ~= "" and savedCombos[selectedCombo] then
            savedCombos[selectedCombo] = nil; deleteComboFile(selectedCombo); comboNamesList = getComboNames()
            if comboDropdownRef then comboDropdownRef:set(comboNamesList) end
            notify("Deleted '" .. selectedCombo .. "'", "Success"); selectedCombo = ""; if comboInfoLabel then comboInfoLabel:set("No combo selected") end
        end
    end })
    comboInfoLabel = ComboPlaySec:Label({ Name = "No combo selected" })

    local PianoTab = Window:Tab({ Name = "Piano", Icon = "lucide:music" })
    local PianoSec = PianoTab:Section({ Name = "MIDI Player", side = "left" })

    local function scanPiano()
        local dn, lm = {}, {}
        for _, p in ipairs(listfiles(PIANO_PATH)) do
            if p:lower():sub(-4) == ".mid" then
                local n = p:match("([^/\\]+)$")
                if n then table.insert(dn, n); lm[n] = p end
            end
        end
        if #dn == 0 then table.insert(dn, "No songs found") end
        table.sort(dn)
        return dn, lm
    end

    local p_init, p_imap = scanPiano()
    piano_fmap = p_imap

    local piano_drop = PianoSec:Dropdown({
        Name = "Song",
        items = p_init,
        default = "None",
        Callback = function(o)
            local p = piano_fmap[o]
            if p then
                local ok, data = pcall(readfile, p)
                if ok then
                    local parsed = parseMidi(data)
                    if #parsed > 0 then
                        piano_fpath, piano_st, piano_idx, piano_lt = p, "Stopped", 1, 0
                        piano_song = parsed
                    end
                end
            end
        end,
    })

    PianoSec:Button({ Name = "🔄 Refresh Songs", Callback = function()
        local dn, lm = scanPiano()
        piano_fmap = lm
        piano_drop:set(dn)
    end})

    PianoSec:Slider({ Name = "Speed", min = 0.25, max = 3, default = 1, Callback = function(v) piano_speed = v end})
    PianoSec:Slider({ Name = "Transpose", min = -12, max = 12, default = 0, Callback = function(v) piano_transpose = v end})
    PianoSec:Toggle({ Name = "Loop", default = false, Callback = function(v) piano_looping = v end})
    PianoSec:Button({ Name = "▶ Play", Callback = function() if #piano_song > 0 then piano_st = "Playing" end end})
    PianoSec:Button({ Name = "⏸ Pause", Callback = function() if piano_st == "Playing" then piano_st = "Paused" end end})
    PianoSec:Button({ Name = "⏹ Stop", Callback = function() piano_st, piano_idx, piano_lt = "Stopped", 1, 0 end})

    local TPTab = Window:Tab({ Name = "Teleports", Icon = "lucide:map-pin" })
    local TPSec = TPTab:Section({ Name = "Locations", side = "left" })
    local TP_LOCATIONS = {
        ["Under the Map"] = Vector3.new(-20.23, -61.53, -146.34), ["Unlicensed Studios"] = Vector3.new(196.86, 23.58, -37.27), ["Towers"] = Vector3.new(25.35, 183.08, 110.77), ["Train Button"] = Vector3.new(182.21, -9.33, 562.54), ["Bowling"] = Vector3.new(267.60, -59.89, -255.06), ["Restaurant"] = Vector3.new(-43.24, 23.63, -83.07), ["Storage House"] = Vector3.new(195.69, 23.58, 151.44), ["Sewers 1"] = Vector3.new(-148.14, -31.48, -127.22), ["Train Station"] = Vector3.new(185.27, -9.69, -97.17), ["Sewers 2"] = Vector3.new(60.84, -10.58, 167.47), ["Shenanigans Mall"] = Vector3.new(155.66, -26.38, -254.85), ["Rhythm Game"] = Vector3.new(12.23, -30.21, -315.03), ["Piano"] = Vector3.new(-86.38, 26.65, -252.48), ["Convenience Store"] = Vector3.new(-247.51, 26.96, -116.64), ["Court"] = Vector3.new(124.48, 23.78, -247.06), ["Graveyard"] = Vector3.new(228.55, 23.68, -130.48), ["Train Station Exit"] = Vector3.new(1.52, 24.72, 396.06), ["Tze's"] = Vector3.new(-55.30, 23.62, 245.42), ["Jail"] = Vector3.new(-243.84, 23.58, 126.97),
    }
    local tpLocationNames = {}
    for name, _ in pairs(TP_LOCATIONS) do table.insert(tpLocationNames, name) end
    table.sort(tpLocationNames)
    local selectedTP = tpLocationNames[1]
    local isTeleporting, TP_DURATION, activeTween = false, 5, nil

    local function dashTeleport(targetPos)
    if isTeleporting then return end
    local character = LocalPlayer.Character
    local root = character and character:FindFirstChild("HumanoidRootPart")
    local humanoid = character and character:FindFirstChildOfClass("Humanoid")
    if not root or not humanoid then return end

    isTeleporting = true
    notify("Surgical Teleport...", "Info")

    humanoid:ChangeState(Enum.HumanoidStateType.Physics)
    local noclipConn
    noclipConn = RunService.Stepped:Connect(function()
        if not character or not character.Parent then return end
        for _, part in pairs(character:GetDescendants()) do
            if part:IsA("BasePart") then part.CanCollide = false end
        end
    end)

    local bv = Instance.new("BodyVelocity")
    bv.MaxForce = Vector3.new(math.huge, math.huge, math.huge)
    bv.Velocity = Vector3.zero
    bv.Parent = root

    task.spawn(function()
        local stepSize = 6 
        local stepDelay = 0.05 
        while isTeleporting and root and root.Parent do
            local currentPos = root.Position
            local distance = (targetPos - currentPos).Magnitude
            if distance <= stepSize then
                root.CFrame = CFrame.new(targetPos)
                break
            end
            local direction = (targetPos - currentPos).Unit
            root.CFrame = root.CFrame + (direction * stepSize)
            pcall(function() ACTeleportRemote:FireServer(tick()) end)
            root.AssemblyLinearVelocity = Vector3.zero
            task.wait(stepDelay)
        end
        local lockStartTime = tick()
        while tick() - lockStartTime < 1.5 do
            root.CFrame = CFrame.new(targetPos)
            root.AssemblyLinearVelocity = Vector3.zero
            pcall(function() ACTeleportRemote:FireServer(tick()) end)
            task.wait(0.2)
        end
        isTeleporting = false
        if noclipConn then noclipConn:Disconnect() end
        if bv then bv:Destroy() end
        if humanoid then humanoid:ChangeState(Enum.HumanoidStateType.Running) end
        notify("Position Validated!", "Success")
    end)
end
    TPSec:Dropdown({ Name = "Location", items = tpLocationNames, default = tpLocationNames[1], Callback = function(V) selectedTP = V end })
    TPSec:Button({ Name = "⚡  Teleport", Callback = function() local pos = TP_LOCATIONS[selectedTP] if pos then dashTeleport(pos) end end })

    local GrabSec = TPTab:Section({ Name = "Item Grabber", side = "right" })
    local function updateItemList()
        local itemsFolder = workspace:FindFirstChild("Items")
        local list = {}
        if itemsFolder then
            for _, item in ipairs(itemsFolder:GetChildren()) do table.insert(list, item.Name) end
        end
        table.sort(list)
        return list
    end

    local itemDropdown = GrabSec:Dropdown({ 
        Name = "Select Item", 
        items = updateItemList(), 
        default = "", 
        Callback = function(V) selectedGrabItem = V end 
    })

    GrabSec:Button({ Name = "🔄  Refresh Items", Callback = function()
        local newList = updateItemList()
        itemDropdown:set(newList)
        notify("Item list updated!", "Success")
    end })

    GrabSec:Button({ Name = "🧲  Grab Item", Callback = function()
        if selectedGrabItem == "" then notify("Select an item first!", "Error") return end
        local itemsFolder = workspace:FindFirstChild("Items")
        local item = itemsFolder and itemsFolder:FindFirstChild(selectedGrabItem)
        if not item then notify("Item no longer exists!", "Error") return end
        local itemPos = item:IsA("Model") and item:GetPivot().Position or item.Position
        task.spawn(function()
            local character = LocalPlayer.Character
            local root = character and character:FindFirstChild("HumanoidRootPart")
            if not root then return end
            local originalCFrame = root.CFrame
            dashTeleport(itemPos) 
            notify("Force-grabbing item...", "Info")
            local lockStartTime = tick()
            local lockDuration = 4 
            local bv = Instance.new("BodyVelocity")
            bv.MaxForce = Vector3.new(math.huge, math.huge, math.huge)
            bv.Velocity = Vector3.zero
            bv.Parent = root
            local prompt = item:FindFirstChildWhichIsA("ProximityPrompt", true)
            local lockConn
            lockConn = RunService.Heartbeat:Connect(function()
                local elapsed = tick() - lockStartTime
                if elapsed < lockDuration then
                    root.CFrame = CFrame.new(itemPos)
                    root.AssemblyLinearVelocity = Vector3.zero
                    if prompt and fireproximityprompt then fireproximityprompt(prompt) end
                else
                    lockConn:Disconnect()
                end
            end)
            task.wait(lockDuration)
            bv:Destroy()
            notify("Returning...", "Info")
            dashTeleport(originalCFrame.Position)
            validatePosition(0.7)
        end)
    end })

    local MiscTab = Window:Tab({ Name = "Misc", Icon = "lucide:pyramid" })
    local MiscSec = MiscTab:Section({ Name = "Character", side = "left" })

    MiscSec:Button({ 
        Name = "💀 Force Reset", 
        Callback = function()
            local character = LocalPlayer.Character
            local root = character and character:FindFirstChild("HumanoidRootPart")
            local humanoid = character and character:FindFirstChildOfClass("Humanoid")
            if not root or not humanoid then return end
            notify("Sinking... (AC Validated)", "Warning")
            humanoid:ChangeState(Enum.HumanoidStateType.Physics)
            local noclipConn
            noclipConn = RunService.Stepped:Connect(function()
                if not character or not character.Parent then return end
                for _, part in pairs(character:GetDescendants()) do
                    if part:IsA("BasePart") then part.CanCollide = false end
                end
            end)
            local bv = Instance.new("BodyVelocity")
            bv.MaxForce = Vector3.new(math.huge, math.huge, math.huge)
            bv.Velocity = Vector3.zero
            bv.Parent = root
            local deathBarrier = workspace.FallenPartsDestroyHeight or -500
            task.spawn(function()
                while character and root and root.Parent do
                    if root.Position.Y < (deathBarrier - 50) then break end
                    root.CFrame = root.CFrame + Vector3.new(0, -3, 0)
                    validatePosition(0.1) 
                    root.AssemblyLinearVelocity = Vector3.zero
                    RunService.Heartbeat:Wait()
                end
                if noclipConn then noclipConn:Disconnect() end
            end)
        end 
    })
    local ESPTab = Window:Tab({ Name = "Player ESP", Icon = "lucide:ghost"})
    local ESPSec = ESPTab:Section({ Name = "Visuals", side = "left" })
    UI_Elements.ESP_CONFIG.Box.Toggle = ESPSec:Toggle({ Name = "Box ESP", default = false, Callback = function(V) ESP_CONFIG.Box.Enabled = V end })
    UI_Elements.ESP_CONFIG.Box.Colorpicker = ESPSec:Colorpicker({ Name = "Box Color", default = ESP_CONFIG.Box.Color, Callback = function(V) ESP_CONFIG.Box.Color = V end })
    UI_Elements.ESP_CONFIG.Name.Toggle = ESPSec:Toggle({ Name = "Name ESP", default = false, Callback = function(V) ESP_CONFIG.Name.Enabled = V end })
    UI_Elements.ESP_CONFIG.Name.Colorpicker = ESPSec:Colorpicker({ Name = "Name Color", default = ESP_CONFIG.Name.Color, Callback = function(V) ESP_CONFIG.Name.Color = V end })
    UI_Elements.ESP_CONFIG.Health.Toggle = ESPSec:Toggle({ Name = "Health ESP", default = false, Callback = function(V) ESP_CONFIG.Health.Enabled = V end })
    UI_Elements.ESP_CONFIG.Health.Colorpicker = ESPSec:Colorpicker({ Name = "Health Color", default = ESP_CONFIG.Health.Color, Callback = function(V) ESP_CONFIG.Health.Color = V end })
    UI_Elements.ESP_CONFIG.Distance.Toggle = ESPSec:Toggle({ Name = "Distance ESP", default = false, Callback = function(V) ESP_CONFIG.Distance.Enabled = V end })
    UI_Elements.ESP_CONFIG.Distance.Colorpicker = ESPSec:Colorpicker({ Name = "Distance Color", default = ESP_CONFIG.Distance.Color, Callback = function(V) ESP_CONFIG.Distance.Color = V end })
    UI_Elements.ESP_CONFIG.Tracer.Toggle = ESPSec:Toggle({ Name = "Tracer ESP", default = false, Callback = function(V) ESP_CONFIG.Tracer.Enabled = V end })
    UI_Elements.ESP_CONFIG.Tracer.Colorpicker = ESPSec:Colorpicker({ Name = "Tracer Color", default = ESP_CONFIG.Tracer.Color, Callback = function(V) ESP_CONFIG.Tracer.Color = V end })
    local ItemSec = ESPTab:Section({ Name = "Item ESP", side = "right" })
    UI_Elements.ESP_CONFIG.Item.Toggle = ItemSec:Toggle({ Name = "Item Highlight", default = false, Callback = function(V) ESP_CONFIG.Item.Enabled = V end })
    UI_Elements.ESP_CONFIG.Item.Colorpicker = ItemSec:Colorpicker({ Name = "Item Color", default = ESP_CONFIG.Item.Color, Callback = function(V) ESP_CONFIG.Item.Color = V end })

    
-- =======================================================
-- 7. UNLOAD LOGIC (FIXED FOR MOBILE)
-- =======================================================
_G.UnloadComboHub = function()
    if isUnloaded then return end
    isUnloaded = true
    isEnabled = false
    LOCK_CONFIG.Enabled = false
    CONFIG.AutoBlock = false
    isComboing = false

    -- 1. Disconnect Core Event Listeners
    if keybindConnection then keybindConnection:Disconnect(); keybindConnection = nil end
    if espConnection then espConnection:Disconnect(); espConnection = nil end
    if blockLockConnection then blockLockConnection:Disconnect(); blockLockConnection = nil end
    if descendantAddedConn then descendantAddedConn:Disconnect(); descendantAddedConn = nil end
    if descendantRemovingConn then descendantRemovingConn:Disconnect(); descendantRemovingConn = nil end
    if comboInputConn then comboInputConn:Disconnect(); comboInputConn = nil end
    RunService:UnbindFromRenderStep("MonolithTargetLock")
    
    if recordConnections then
        for _, conn in pairs(recordConnections) do conn:Disconnect() end
        recordConnections = {}
    end

    if trackedAnimators then
        for _, conn in pairs(trackedAnimators) do
            if conn then conn:Disconnect() end
        end
        trackedAnimators = {}
    end

    -- 2. Restore Player Character
    local localChar = LocalPlayer.Character
    if localChar then
        local root = localChar:FindFirstChild("HumanoidRootPart")
        if LockBodyGyro then LockBodyGyro:Destroy(); LockBodyGyro = nil end
        local hum = localChar:FindFirstChildOfClass("Humanoid")
        if hum then hum.AutoRotate = true end
    end

    -- 3. Destroy All ESP
    for p in pairs(ESP_Cache) do RemoveESP(p) end
    for _, t in pairs(ItemTexts) do t:Remove() end
    for _, h in pairs(ItemHighlights) do h:Destroy() end
    ESP_Cache = {}
    ItemTexts = {}
    ItemHighlights = {}

    -- 4. FORCED UI CLEANUP (Search by Name)
    -- This looks in every possible location for the UIs and kills them
    local possibleParents = {
        (gethui and gethui()), 
        game:GetService("CoreGui"), 
        LocalPlayer:WaitForChild("PlayerGui")
    }

    for _, parent in pairs(possibleParents) do
        if parent then
            local mainUI = parent:FindFirstChild("MonolithUI")
            if mainUI then mainUI:Destroy() end
            
            local mobileUI = parent:FindFirstChild("MonolithMobileGui")
            if mobileUI then mobileUI:Destroy() end
        end
    end

    -- 5. Clean Globals
    _G.ToggleMyMenu = nil
    _G.UnloadComboHub = nil

    print("✅ Sedse Hub fully unloaded: All UIs cleared!")
end

-- Hook UI closing to trigger unload
task.spawn(function()
    task.wait(1)
    local targetParent
    pcall(function() targetParent = (gethui and gethui()) or CoreGui end)
    if not targetParent then targetParent = LocalPlayer:WaitForChild("PlayerGui") end
    
    local ui = targetParent:FindFirstChild("MonolithUI")
    if ui then 
        ui.AncestryChanged:Connect(function(_, parent) 
            if not parent and _G.UnloadComboHub then _G.UnloadComboHub() end 
        end) 
    end
end)

-- =======================================================
-- MOBILE SUPPORT ENGINE (UPDATED V2)
-- =======================================================
local isMobile = UserInputService.TouchEnabled

if isMobile then
    -- Replace the targetParent block in the Mobile Section with this:
    local targetParent = (gethui and gethui()) or game:GetService("CoreGui") or LocalPlayer:WaitForChild("PlayerGui")

    local MobileGui = Instance.new("ScreenGui")
    MobileGui.Name = "MonolithMobileGui"
    MobileGui.ResetOnSpawn = false
    MobileGui.ZIndexBehavior = Enum.ZIndexBehavior.Global
    MobileGui.Parent = targetParent

    local function createMobileButton(name, text, position, callback)
        local btn = Instance.new("TextButton")
        btn.Name = name
        btn.Size = UDim2.new(0, 65, 0, 65)
        btn.Position = position
        btn.AnchorPoint = Vector2.new(0.5, 0.5)
        btn.BackgroundColor3 = Color3.fromRGB(20, 20, 20)
        btn.TextColor3 = Color3.fromRGB(255, 255, 255)
        btn.Text = text
        btn.Font = Enum.Font.GothamBold
        btn.TextSize = 12
        btn.AutoButtonColor = true
        btn.ZIndex = 9999
        btn.Parent = MobileGui

        local corner = Instance.new("UICorner")
        corner.CornerRadius = UDim.new(1, 0)
        corner.Parent = btn

        local stroke = Instance.new("UIStroke")
        stroke.Thickness = 2
        stroke.Color = Color3.fromRGB(100, 150, 255)
        stroke.Parent = btn

        local dragging, dragStart, startPos = false, nil, nil
        btn.InputBegan:Connect(function(input)
            if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
                dragging = true; dragStart = input.Position; startPos = btn.Position
            end
        end)

        UserInputService.InputChanged:Connect(function(input)
            if dragging and (input.UserInputType == Enum.UserInputType.MouseMovement or input.UserInputType == Enum.UserInputType.Touch) then
                local delta = input.Position - dragStart
                btn.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
            end
        end)

        UserInputService.InputEnded:Connect(function(input)
            if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
                dragging = false
            end
        end)

        local isDrag = false
        btn.InputChanged:Connect(function() if dragging then isDrag = true end end)

        btn.MouseButton1Click:Connect(function()
            if not isDrag then callback() end
            isDrag = false
        end)
        
        task.spawn(function()
            while task.wait(1) do if stroke then stroke.Color = uiAccentColor or Color3.fromRGB(100, 150, 255) end end
        end)

        return btn
    end

    -- 3. Create "ATTACK" Button
    createMobileButton("MobileAttackBtn", "BLACKFLASH", UDim2.new(0.85, 0, 0.7, 0), function()
        if isEnabled then
            executeSmoothArchCombo()
        else
            notify("Enable 'Auto BlackFlash Chain' in the menu first!", "Warning")
        end
    end)

    -- 4. Create "TOGGLE MENU" Button (FIXED)
    -- 4. Create "TOGGLE MENU" Button (100% RELIABLE FIX)
    createMobileButton("MobileMenuBtn", "MENU", UDim2.new(0.15, 0, 0.15, 0), function()
        if _G.ToggleMyMenu then
            _G.ToggleMyMenu()
        else
            notify("Menu is still loading or UI failed to load.", "Error")
        end
    end)
    
    local oldUnload = _G.UnloadComboHub
    _G.UnloadComboHub = function()
        if oldUnload then oldUnload() end
        if MobileGui then MobileGui:Destroy() end
    end
end
keybindConnection = UserInputService.InputBegan:Connect(function(input, gp)
    if not gp and input.KeyCode == CONFIG.ActivationKey and isEnabled then
        executeSmoothArchCombo()
    end
end)

print("--- Hub Loaded: Combat active, UI protected ---")
