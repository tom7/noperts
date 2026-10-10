# Blender: color the selected object by a code texture from
# `codebdd --texture=BASE` (BASE.png). Run from Blender's Text Editor with the
# object selected, after setting IMAGE. The object should be in the texture's
# frame (BASE.stl is; scale does not matter); each surface point gets the
# color of its direction from the object's origin.
import bpy

IMAGE = "/path/to/BASE.png"

obj = bpy.context.active_object
mat = bpy.data.materials.new("codes")
mat.use_nodes = True
nodes, links = mat.node_tree.nodes, mat.node_tree.links
bsdf = nodes["Principled BSDF"]
coords = nodes.new("ShaderNodeTexCoord")
env = nodes.new("ShaderNodeTexEnvironment")
env.image = bpy.data.images.load(IMAGE)
env.interpolation = "Closest"  # crisp code boundaries
links.new(coords.outputs["Object"], env.inputs["Vector"])
links.new(env.outputs["Color"], bsdf.inputs["Base Color"])
obj.data.materials.clear()
obj.data.materials.append(mat)
